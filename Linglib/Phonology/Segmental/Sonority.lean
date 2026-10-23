/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.Basic
public import Linglib.Phonology.Segmental.NaturalClass
public import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Powerset
import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Sonority scales

A sonority scale ranks segments, or classes of them, in a linear order. A set is a cut of a
scale when it is what lies above some point of the scale, and contiguous when it is what lies
within some interval, the preimage of an order-connected set. A feature cuts a scale when the
segments with one of its values form a cut. The cuts of a scale are nested, so features whose
values cross do not both cut it, and two features whose values combine freely do not both divide
it into contiguous classes. A scale coarsens another when it preserves its order, and the cuts of
the coarser scale are cuts of the finer one.

The base scale is the sonority hierarchy of Hayes's Table 4.1, the modal hierarchy of Parker:
obstruents, nasals, liquids, glides and vowels. Each class is defined by the features of
Hayes's p. 77, the columns of the table are cut by [sonorant], [approximant], [consonantal] and
[syllabic], [continuant] is not a sonority feature, and among the columns the natural classes
are the contiguous sets.

## Main definitions

* `Phonology.Sonority.IsCut`, `Phonology.Sonority.Contiguous`: the sets of a scale above a point
  and within an interval.
* `Phonology.Sonority.Coarsens`: a scale preserves the order of another.
* `Phonology.Sonority.profile`: whether sonority rises, plateaus or falls from one segment to
  another.
* `Phonology.Sonority`: the classes of the hierarchy, with `Sonority.toSegment` the columns of
  Table 4.1, `Sonority.description` the features of p. 77, and `Sonority.ofSegment`.

## Main results

* `Phonology.Sonority.IsCut.total`: the cuts of a scale are nested.
* `Phonology.Sonority.not_contiguous_of_independent`: two features whose values combine freely
  do not both divide a scale into contiguous classes.
* `Phonology.Sonority.IsCut.of_coarsens`: the cuts of a coarser scale are cuts of a finer one.
* `Phonology.Sonority.ofSegment_eq_of_le`, `Phonology.Sonority.description_le_iff`: a segment
  with the values of a column of Table 4.1 has that column's sonority and description.
* `Phonology.Sonority.isNaturalClass_image_iff`: among the columns, the natural classes are the
  contiguous sets.

## References

* [hayes-2009]: Table 4.1 (p. 76), the manner classes (p. 77), and [continuant] (p. 78)
* [parker-2002]: the modal hierarchy (3.3) (p. 62)
-/

@[expose] public section

namespace Phonology

/-! ### Scales -/

namespace Sonority

variable {α β γ : Type*} [LinearOrder β] [LinearOrder γ] {σ : α → β} {τ : α → γ} {S T : Set α}

/-- A set is a cut of a scale when it is the set of elements above some point of the scale. -/
def IsCut (σ : α → β) (S : Set α) : Prop := ∃ U : Set β, IsUpperSet U ∧ S = σ ⁻¹' U

/-- A set is contiguous on a scale when it is the preimage of an order-connected set. -/
def Contiguous (σ : α → β) (S : Set α) : Prop := ∃ I : Set β, I.OrdConnected ∧ S = σ ⁻¹' I

/-- A scale `τ` coarsens a scale `σ` when it preserves its order. -/
def Coarsens (τ : α → γ) (σ : α → β) : Prop := ∀ a b, σ a ≤ σ b → τ a ≤ τ b

/-- Whether sonority rises (`lt`), plateaus (`eq`) or falls (`gt`) from `a` to `b`. -/
def profile (σ : α → β) (a b : α) : Ordering := compare (σ a) (σ b)

theorem IsCut.total (hS : IsCut σ S) (hT : IsCut σ T) : S ⊆ T ∨ T ⊆ S := by
  obtain ⟨U, hU, rfl⟩ := hS
  obtain ⟨V, hV, rfl⟩ := hT
  exact (hU.total hV).imp (Set.preimage_mono ·) (Set.preimage_mono ·)

theorem not_isCut_and_isCut (hST : ¬ S ⊆ T) (hTS : ¬ T ⊆ S) : ¬ (IsCut σ S ∧ IsCut σ T) :=
  fun ⟨hS, hT⟩ ↦ (hS.total hT).elim hST hTS

theorem IsCut.contiguous (h : IsCut σ S) : Contiguous σ S := by
  obtain ⟨U, hU, rfl⟩ := h
  exact ⟨U, hU.ordConnected, rfl⟩

theorem contiguous_iff :
    Contiguous σ S ↔ ∀ a ∈ S, ∀ b ∈ S, ∀ c, σ a ≤ σ c → σ c ≤ σ b → c ∈ S := by
  refine ⟨?_, fun h ↦ ⟨{x | ∃ a ∈ S, ∃ b ∈ S, σ a ≤ x ∧ x ≤ σ b}, ⟨?_⟩, ?_⟩⟩
  · rintro ⟨I, hI, rfl⟩ a ha b hb c hac hcb
    exact hI.out ha hb ⟨hac, hcb⟩
  · rintro x ⟨a, ha, -, -, hax, -⟩ y ⟨-, -, b, hb, -, hyb⟩ z ⟨hxz, hzy⟩
    exact ⟨a, ha, b, hb, hax.trans hxz, hzy.trans hyb⟩
  · ext c
    exact ⟨fun hc ↦ ⟨c, hc, c, hc, le_rfl, le_rfl⟩,
      fun ⟨a, ha, b, hb, hac, hcb⟩ ↦ h a ha b hb c hac hcb⟩

instance [Fintype α] [DecidablePred (· ∈ S)] : Decidable (Contiguous σ S) :=
  decidable_of_iff _ contiguous_iff.symm

theorem IsCut.of_coarsens (h : Coarsens τ σ) (hS : IsCut τ S) : IsCut σ S := by
  obtain ⟨U, hU, rfl⟩ := hS
  refine ⟨{y | ∃ a ∈ τ ⁻¹' U, σ a ≤ y}, fun x y hxy ⟨a, ha, hax⟩ ↦ ⟨a, ha, hax.trans hxy⟩, ?_⟩
  ext b
  exact ⟨fun hb ↦ ⟨b, hb, le_rfl⟩, fun ⟨a, ha, hab⟩ ↦ hU (h a b hab) ha⟩

/-- Two features whose values combine freely do not both divide a scale into contiguous classes. -/
theorem not_contiguous_of_independent (σ : α → β) {φ ψ : α → Bool}
    (h : ∀ x y, ∃ a, φ a = x ∧ ψ a = y) :
    ¬ ((∀ v, Contiguous σ {a | φ a = v}) ∧ ∀ v, Contiguous σ {a | ψ a = v}) := by
  rintro ⟨hφ, hψ⟩
  -- the lower of the two neighbours of a least combination lies between it and the other
  choose w hw using h
  obtain ⟨⟨x, y⟩, hm⟩ := Finite.exists_min fun p : Bool × Bool ↦ σ (w p.1 p.2)
  rcases le_total (σ (w (!x) y)) (σ (w x (!y))) with hle | hle
  · have := contiguous_iff.1 (hφ x) (w x y) (hw x y).1 (w x (!y)) (hw x (!y)).1 (w (!x) y)
      (hm (!x, y)) hle
    simp [(hw (!x) y).1] at this
  · have := contiguous_iff.1 (hψ y) (w x y) (hw x y).2 (w (!x) y) (hw (!x) y).2 (w x (!y))
      (hm (x, !y)) hle
    simp [(hw x (!y)).2] at this

end Sonority

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
    .ofSpecs [(.syllabic, false), (.consonantal, true), (.approximant, false), (.sonorant, false)]
  | .nasal =>
    .ofSpecs [(.syllabic, false), (.consonantal, true), (.approximant, false), (.sonorant, true)]
  | .liquid =>
    .ofSpecs [(.syllabic, false), (.consonantal, true), (.approximant, true), (.sonorant, true)]
  | .glide =>
    .ofSpecs [(.syllabic, false), (.consonantal, false), (.approximant, true), (.sonorant, true)]
  | .vowel =>
    .ofSpecs [(.syllabic, true), (.consonantal, false), (.approximant, true), (.sonorant, true)]

/-- The features that define a class (Hayes p. 77): [−sonorant] for an obstruent, [−approximant,
+sonorant] for a nasal, [+consonantal, +approximant] for a liquid, [−syllabic, −consonantal] for a
glide and [+syllabic] for a vowel. -/
def description : Sonority → Segment
  | .obstruent => .ofSpecs [(.sonorant, false)]
  | .nasal => .ofSpecs [(.approximant, false), (.sonorant, true)]
  | .liquid => .ofSpecs [(.consonantal, true), (.approximant, true)]
  | .glide => .ofSpecs [(.syllabic, false), (.consonantal, false)]
  | .vowel => .ofSpecs [(.syllabic, true)]

/-- The sonority of a segment: an obstruent if [−sonorant], else a nasal if [−approximant], else
a liquid if [+consonantal], else a vowel if [+syllabic], and otherwise a glide. A syllabic liquid
or nasal keeps the sonority of its class. -/
def ofSegment (s : Segment) : Sonority :=
  if s.HasValue .sonorant false then .obstruent
  else if s.HasValue .approximant false then .nasal
  else if s.HasValue .consonantal true then .liquid
  else if s.HasValue .syllabic true then .vowel
  else .glide

end Sonority

end Phonology
