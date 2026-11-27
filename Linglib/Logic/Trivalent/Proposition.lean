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

A **trivalent proposition** is true, false or undefined at each world. It divides the worlds three
ways: its **positive extension**, where it is true, its **negative extension**, where it is false,
and its **gap**, where it is neither. On Strawson's view *The King of France is bald* has in its gap
the worlds with no king of France. A proposition is fixed by its two extensions, and any two
disjoint sets of worlds are the extensions of one. Negation swaps them.

Presupposing more widens the gap: the **restriction** of a proposition to a condition keeps its
value where the condition holds and is undefined elsewhere. A restricted two-valued proposition is a
**conditional event** in de Finetti's sense, and every trivalent proposition is one, its truth on
the condition that it is defined.

## Implementation notes

The two extensions are a bounded lattice embedding into Fitting's product of the sets of worlds with
itself, natural in the worlds. It carries Kleene's negation to the swap and transplication to
Fitting's guard. The assertion operator of Beaver and Krahmer, applied at each world, moves the gap
into the negative extension. In the knowledge order a restriction lies below the proposition it
restricts, and the propositions below a two-valued one are the conditional events that assert it.

## References

* [beaver-krahmer-2001]
* [de-finetti-1936]
* [fitting-1994]
* [beaver-geurts-denlinger-2021]
-/

@[expose] public section

namespace Trivalent

open Bilattice Product

variable {W : Type*}

/-!
### Extensions

The worlds where a proposition is true, where it is false and where it is undefined cover all the
worlds and do not overlap. The first two sets determine the proposition, and they turn the Strong
Kleene connectives into operations on pairs of sets.
-/

/-- The **positive extension** of a proposition is the set of worlds where it is true. -/
def posExt (p : W → Trivalent) : Set W := {w | p w = .true}

/-- The **negative extension** of a proposition is the set of worlds where it is false. -/
def negExt (p : W → Trivalent) : Set W := {w | p w = .false}

/-- The **gap** of a proposition is the set of worlds where it is undefined. -/
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

/-- The **extensions** of a trivalent proposition are the pair of its positive extension, the worlds
where it is true, and its negative extension, the worlds where it is false. Taking extensions
preserves the truth order: the extensions of a strong Kleene conjunction are the meet of the two
pairs, and those of a disjunction their join. -/
def extensions : BoundedLatticeHom (W → Trivalent) (Set W ⊙ Set W) where
  toFun p := mk (posExt p) (negExt p)
  map_sup' p q := by ext w <;> simp [posExt, negExt]
  map_inf' p q := by ext w <;> simp [posExt, negExt]
  map_top' := by ext w <;> simp [posExt, negExt]
  map_bot' := by ext w <;> simp [posExt, negExt]

theorem extensions_apply (p : W → Trivalent) : extensions p = mk (posExt p) (negExt p) := rfl

@[simp] theorem pro_extensions (p : W → Trivalent) : (extensions p).pro = posExt p := rfl
@[simp] theorem con_extensions (p : W → Trivalent) : (extensions p).con = negExt p := rfl

/-- If a proposition is evaluated through a map from other worlds, its extensions are the preimages
of the original extensions under that map. -/
theorem extensions_comp {W' : Type*} (f : W' → W) (p : W → Trivalent) :
    extensions (p ∘ f) = mk (f ⁻¹' posExt p) (f ⁻¹' negExt p) := rfl

theorem extensions_le_extensions : extensions p ≤ extensions q ↔ p ≤ q := by
  have key : ∀ a b : Trivalent, a ≤ b ↔ (a = .true → b = .true) ∧ (b = .false → a = .false) := by
    decide
  simp only [extensions_apply, mk_le_mk, Set.subset_def, mem_posExt, mem_negExt, Pi.le_def, key]
  exact ⟨fun h w ↦ ⟨h.1 w, h.2 w⟩, fun h ↦ ⟨fun w ↦ (h w).1, fun w ↦ (h w).2⟩⟩

theorem extensions_injective : Function.Injective (extensions (W := W)) := fun _ _ h ↦
  le_antisymm (extensions_le_extensions.1 h.le) (extensions_le_extensions.1 h.ge)

/-- The positive and negative extensions of a proposition never overlap, and every pair of sets of
worlds that do not overlap is the pair of extensions of some proposition. These are the pairs
Fitting calls consistent. -/
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

/-- Trivalent propositions correspond one to one to the pairs of sets of worlds that do not overlap,
and the correspondence respects the truth order. -/
noncomputable def orderIsoDisjoint :
    (W → Trivalent) ≃o {x : Set W ⊙ Set W | Disjoint x.pro x.con} :=
  (OrderEmbedding.ofMapLEIff extensions fun _ _ ↦ extensions_le_extensions).orderIso.trans
    (Set.orderIsoOfEq _ _ range_extensions)

/-- Negating a proposition swaps its extensions. -/
@[simp] theorem extensions_compl (p : W → Trivalent) : extensions pᶜ = (extensions p)ᶜ := by
  ext w <;> simp [posExt, negExt]

/-- The extensions of *φ* presupposing *π*, taken world by world, are the extensions of *φ* cut down
to the worlds where *π* is true. On pairs of sets this operation is Fitting's guard. -/
theorem extensions_transplication (π φ : W → Trivalent) :
    extensions (fun w ↦ transplication (π w) (φ w)) = guard (extensions π) (extensions φ) := by
  ext w <;> simp [posExt, negExt, transplication_eq_true_iff, transplication_eq_false_iff]

end Extensions

/-- A proposition is **bivalent** when it is true or false at every world. -/
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

/-!
### Extensions under assertion

Asserting a proposition, world by world, makes it two-valued: its positive extension stays and its
gap joins its negative extension. Conjoining a proposition with a two-valued condition keeps its gap
only where the condition holds.
-/

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

/-- Applying to a proposition, world by world, an operation on truth values that returns undefined
exactly when it is given undefined leaves the gap unchanged. -/
theorem gapExt_comp {f : Trivalent → Trivalent} (hf : ∀ a, f a = .undefined ↔ a = .undefined)
    (p : W → Trivalent) :
    gapExt (f ∘ p) = gapExt p := by
  ext w; simp [hf]

/-- Applying to a proposition, world by world, an operation on truth values that never returns
undefined gives a bivalent proposition. -/
theorem isBivalent_comp {f : Trivalent → Trivalent} (hf : ∀ a, f a ≠ .undefined)
    (p : W → Trivalent) :
    IsBivalent (f ∘ p) :=
  (isBivalent_iff_forall_ne_undefined _).2 fun _ ↦ hf _

theorem isBivalent_ofProp_eq_true (p : W → Trivalent) : IsBivalent fun w ↦ ofProp (p w = .true) :=
  fun w ↦ by by_cases h : p w = .true <;> simp [h]

/-!
### Restriction

A proposition that presupposes something more is undefined wherever the added presupposition fails.
This is its **restriction**, Blamey's transplication taken world by world.
-/

section Restrict

/-- The **restriction** of a proposition to a condition has the proposition's value at the worlds
where the condition holds and is undefined at the others. It is the proposition with the condition
added as a presupposition. -/
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

/-- At every world a restriction is either undefined or has the value of the proposition it
restricts, so it never carries more information. -/
theorem restrict_kLE : Trivalent.restrict A p w ≤ₖ p w := transplication_kLE _ _

end Restrict

/-!
### Conditional events

A **conditional event**, written *B | A*, asserts *B* on the condition *A*: it is true where both
hold, false where *A* holds and *B* does not, and undefined where *A* fails. The notion is de
Finetti's. Every trivalent proposition is a conditional event, and two conditional events are the
same when they have the same condition and agree where it holds.
-/

section ConditionalEvent

/-- The **conditional event** *B | A* has the classical value of *B* at the worlds where *A* holds
and is undefined at the others. The notion is de Finetti's. -/
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

/-- At every world a conditional event *B | A* is either undefined or has the classical value of
*B*, so it never carries more information than *B*. -/
theorem condEvent_kLE : condEvent A B w ≤ₖ ofProp (B w) := transplication_kLE _ _

/-- A proposition is at every world either undefined or of the same value as a two-valued
proposition *B* exactly when it is the conditional event of *B* on the condition that it is
defined. -/
theorem forall_kLE_ofProp_iff {p : W → Trivalent} :
    (∀ w, p w ≤ₖ ofProp (B w)) ↔ p = condEvent (p · ≠ .undefined) B := by
  refine ⟨fun h ↦ funext fun w ↦ ?_, fun h w ↦ ?_⟩
  · have := kLE_ofProp_iff.1 (h w)
    cases hp : p w <;> simp_all [condEvent]
  · rw [h]; exact condEvent_kLE

end

/-- Every trivalent proposition is the conditional event *B | A* in which *A* is the condition that
it is defined and *B* the condition that it is true. -/
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
