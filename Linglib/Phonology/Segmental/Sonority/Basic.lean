/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.Basic
public import Linglib.Phonology.Segmental.NaturalClass
public import Linglib.Core.Order.OrdConnected
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Linglib.Phonology.Segmental.PHOIBLE

/-!
# The sonority hierarchy

`Phonology.Sonority` is the hierarchy of obstruents, nasals, liquids, glides and vowels, a linear
order. `Sonority.toSegment` gives each class its values for [sonorant], [approximant],
[consonantal] and [syllabic], and each of the four features holds on an upper set of the
hierarchy, `Set.Ici` of a class (`Phonology.Sonority.setOf_toSegment_eq_Ici`). `Sonority.ofSegment`
reads the class of a segment off the four features, and a segment with the values of a class has
that class (`Phonology.Sonority.ofSegment_eq_of_le`). Among the classes, the natural classes are
the order-connected sets (`Phonology.Sonority.isNaturalClass_image_iff`).

A sonority scale is a map `σ : α → β` from segments, or classes of them, to a linear order. A set
of segments is contiguous on `σ` when it is `Set.OrdConnectedAlong σ`, the preimage of an
order-connected set; the segments that are [+continuant] are not contiguous on `ofSegment`. A
scale `τ` coarsens `σ` when `σ a ≤ σ b` implies `τ a ≤ τ b`
(`Phonology.Sonority.Coarsens`), and the sets contiguous on a coarser scale are contiguous on a
finer one.

## References

* [hayes-2009]
* [parker-2002]
-/

@[expose] public section

namespace Phonology

/-! ### The sonority hierarchy -/

/-- The sonority hierarchy, from least to most sonorous. -/
inductive Sonority where
  /-- The obstruents, [−sonorant]. -/
  | obstruent
  /-- The nasals, [−approximant, +sonorant]. -/
  | nasal
  /-- The liquids, [+consonantal, +approximant]. -/
  | liquid
  /-- The glides, [−syllabic, −consonantal]. -/
  | glide
  /-- The vowels, [+syllabic]. -/
  | vowel
  deriving DecidableEq, Repr, Fintype

namespace Sonority

/-- The position of a class on the hierarchy, the obstruents at 0. -/
def rank : Sonority → ℕ
  | .obstruent => 0 | .nasal => 1 | .liquid => 2 | .glide => 3 | .vowel => 4

instance : LinearOrder Sonority :=
  LinearOrder.lift' rank fun a b h ↦ by cases a <;> cases b <;> simp_all [rank]

/-- The column of a class in Table 4.1: its values for [syllabic], [consonantal], [approximant]
and [sonorant], the four features that cut the hierarchy. -/
def toSegment : Sonority → Segment
  | .obstruent =>
    [−syllabic, +consonantal, −approximant, −sonorant]
  | .nasal =>
    [−syllabic, +consonantal, −approximant, +sonorant]
  | .liquid =>
    [−syllabic, +consonantal, +approximant, +sonorant]
  | .glide =>
    [−syllabic, −consonantal, +approximant, +sonorant]
  | .vowel =>
    [+syllabic, −consonantal, +approximant, +sonorant]

/-- The features that define a class (Hayes p. 77): [−sonorant] for an obstruent, [−approximant,
+sonorant] for a nasal, [+consonantal, +approximant] for a liquid, [−syllabic, −consonantal] for a
glide and [+syllabic, −consonantal] for a vowel. Hayes lists a vowel as [+syllabic] with the
complication of the syllabic consonants left to his next section, and his Table 4.1 has it
[−consonantal]. -/
def description : Sonority → Segment
  | .obstruent => [−sonorant]
  | .nasal => [−approximant, +sonorant]
  | .liquid => [+consonantal, +approximant]
  | .glide => [−syllabic, −consonantal]
  | .vowel => [+syllabic, −consonantal]

/-- The sonority of a segment: an obstruent if [−sonorant], else a nasal if [−approximant], else
a liquid if [+consonantal], else a vowel if [+syllabic], and otherwise a glide. A syllabic liquid
or nasal keeps the sonority of its class. -/
def ofSegment (s : Segment) : Sonority :=
  if s .sonorant = false then .obstruent
  else if s .approximant = false then .nasal
  else if s .consonantal = true then .liquid
  else if s .syllabic = true then .vowel
  else .glide

theorem rank_strictMono : StrictMono rank := fun _ _ h ↦ h

/-! ### Scales -/

section Scale

variable {α β γ : Type*} [Preorder β] [Preorder γ] {σ : α → β} {τ : α → γ} {S : Set α}

/-- A scale `τ` coarsens a scale `σ` when it preserves its order. -/
def Coarsens (τ : α → γ) (σ : α → β) : Prop := ∀ a b, σ a ≤ σ b → τ a ≤ τ b

/-- A set contiguous on a coarser scale is contiguous on a finer one. -/
theorem Coarsens.ordConnectedAlong (h : Coarsens τ σ) (hS : S.OrdConnectedAlong τ) :
    S.OrdConnectedAlong σ :=
  hS.of_le_imp_le h

end Scale

/-- Table 4.1: [sonorant], [approximant], [consonantal] and [syllabic] each hold on an upper set
of the hierarchy. -/
theorem setOf_toSegment_eq_Ici :
    {c : Sonority | c.toSegment .sonorant = true} = Set.Ici nasal ∧
      {c : Sonority | c.toSegment .approximant = true} = Set.Ici liquid ∧
      {c : Sonority | c.toSegment .consonantal = false} = Set.Ici glide ∧
      {c : Sonority | c.toSegment .syllabic = true} = Set.Ici vowel := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext c
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    cases c <;> decide

/-- The features `ofSegment` reads, the four of Table 4.1. -/
def features : Finset Feature := {.sonorant, .approximant, .consonantal, .syllabic}

theorem ofSegment_congr {s s' : Segment} (h : ∀ f ∈ features, s f = s' f) :
    ofSegment s = ofSegment s' := by
  simp only [ofSegment, h _ (by decide : Feature.sonorant ∈ features),
    h _ (by decide : Feature.approximant ∈ features),
    h _ (by decide : Feature.consonantal ∈ features),
    h _ (by decide : Feature.syllabic ∈ features)]

theorem ofSegment_setFeature {f : Feature} (hf : f ∉ features) (s : Segment) (v : Bool) :
    ofSegment (s.setFeature f v) = ofSegment s :=
  ofSegment_congr fun g hg ↦ Segment.setFeature_apply_of_ne (by rintro rfl; exact hf hg) s v

@[simp] theorem ofSegment_toSegment (c : Sonority) : ofSegment c.toSegment = c := by
  cases c <;> decide

theorem apply_eq_toSegment_of_le {c : Sonority} {s : Segment}
    (h : c.toSegment ≤ s) {f : Feature} (hf : f ∈ features) :
    s f = c.toSegment f := by
  have key : ∀ c : Sonority, ∀ f ∈ features, ∃ v, c.toSegment f = some v := by decide
  obtain ⟨v, hv⟩ := key c f hf
  rw [hv]
  exact h f v hv

/-- A segment with the values of a column of Table 4.1 has that column's sonority. -/
theorem ofSegment_eq_of_le {c : Sonority} {s : Segment} (h : c.toSegment ≤ s) :
    ofSegment s = c :=
  (ofSegment_congr fun _ hf ↦ apply_eq_toSegment_of_le h hf).trans (ofSegment_toSegment c)

/-- On a segment with the values of a column of Table 4.1, exactly that column's description
holds. -/
theorem description_le_iff {c c' : Sonority} {s : Segment} (h : c.toSegment ≤ s) :
    c'.description ≤ s ↔ c' = c := by
  have hsupp : ∀ c' : Sonority, ∀ f v, c'.description f = some v → f ∈ features := by decide
  have key : ∀ c c' : Sonority, c'.description ≤ c.toSegment ↔ c' = c := by decide
  rw [← key c c']
  exact forall₂_congr fun f v ↦ imp_congr_right fun hv ↦ by
    rw [apply_eq_toSegment_of_le h (hsupp c' f v hv)]

theorem description_le_iff_ofSegment_eq {c c' : Sonority} {s : Segment}
    (h : c.toSegment ≤ s) : c'.description ≤ s ↔ ofSegment s = c' := by
  rw [description_le_iff h, ofSegment_eq_of_le h, eq_comm]

/-- The sonority rise from `a` to `b` is positive when sonority rises, zero on a plateau,
and negative when it falls. -/
def rise (a b : Sonority) : ℤ := b.rank - a.rank

@[simp] theorem rise_self (a : Sonority) : rise a a = 0 := by simp only [rise]; omega

theorem neg_rise (a b : Sonority) : -rise a b = rise b a := by simp only [rise]; omega

theorem rise_add_rise (a b c : Sonority) : rise a b + rise b c = rise a c := by
  simp only [rise]; omega

@[simp] theorem rise_pos {a b : Sonority} : 0 < rise a b ↔ a < b := by
  change 0 < (b.rank : ℤ) - a.rank ↔ a.rank < b.rank; omega

@[simp] theorem rise_neg {a b : Sonority} : rise a b < 0 ↔ b < a := by
  change (b.rank : ℤ) - a.rank < 0 ↔ b.rank < a.rank; omega

@[simp] theorem rise_eq_zero {a b : Sonority} : rise a b = 0 ↔ a = b :=
  ⟨fun h ↦ rank_strictMono.injective (by simp only [rise] at h; omega),
    by rintro rfl; exact rise_self _⟩

/-- [continuant] is not a sonority feature: its positive class is not contiguous on the hierarchy
(p. 78). -/
theorem not_ordConnectedAlong_continuant :
    ¬ {s : Segment | s .continuant = true}.OrdConnectedAlong ofSegment := by
  intro h
  exact absurd (Set.ordConnectedAlong_iff.1 h ([−sonorant, +continuant]) (by decide)
    ([+syllabic, +sonorant, +approximant, +continuant])
    (by decide) ([+sonorant, −approximant, −continuant])
    (by decide) (by decide)) (by decide)

theorem naturalClass_description (c : Sonority) :
    naturalClass c.description (Finset.univ.image Sonority.toSegment) = {c.toSegment} := by
  revert c
  decide +kernel

/-- Among the columns of Table 4.1, the natural classes are the contiguous sets (p. 76). -/
theorem isNaturalClass_image_iff {S : Finset Sonority} :
    IsNaturalClass (Finset.univ.image Sonority.toSegment) (S.image Sonority.toSegment) ↔
      (S : Set Sonority).OrdConnected := by
  simp only [Set.ordConnected_iff, Finset.mem_coe, Set.subset_def, Set.mem_Icc]
  have key : ∀ S : Finset Sonority,
      (IsNaturalClass (Finset.univ.image toSegment) (S.image toSegment) ↔
        ∀ a ∈ S, ∀ b ∈ S, a ≤ b → ∀ c, a ≤ c ∧ c ≤ b → c ∈ S) := by
    decide +kernel
  exact key S

open Data.PHOIBLE.FeatureMatrix in
/-- Chart segments fall into the sonority classes of their glyphs, the nasal by its
[−approximant]. -/
example : [«p», «s», «n», «l», «j», «a»].map (ofSegment ∘ Data.PHOIBLE.FeatureMatrix.toSegment) =
    [.obstruent, .obstruent, .nasal, .liquid, .glide, .vowel] := by decide

end Sonority

namespace Segment

variable (s : Segment)

theorem isVowel_iff_le : s.IsVowel ↔ Sonority.vowel.description ≤ s := by
  simp [Sonority.description, IsVowel, IsSyllabic]

theorem isObstruent_iff_le : s.IsObstruent ↔ Sonority.obstruent.description ≤ s := by
  simp [Sonority.description, IsObstruent]

theorem isNasal_iff_le : s.IsNasal ↔ Sonority.nasal.description ≤ s := by
  simp [Sonority.description, IsNasal]

end Segment

end Phonology
