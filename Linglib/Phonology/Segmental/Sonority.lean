/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.Basic
public import Linglib.Phonology.Segmental.NaturalClass
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Sonority scales

A sonority scale ranks segments, or classes of them, in a linear order. A set is a cut of a
scale when it is what the scale places in an upper set of its points, and contiguous when it is
what lies within some interval, the preimage of an order-connected set. A feature cuts a scale
when the segments with one of its values form a cut. The cuts of a scale are nested, as the upper
sets of a linear order are, so features whose values cross do not both cut it, and two features
whose values combine freely do not both divide it into contiguous classes. A scale coarsens another when it preserves its order, and the cuts of
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

/-- A set is a cut of a scale when it is what the scale places in an upper set of its points. -/
def IsCut (σ : α → β) (S : Set α) : Prop := ∃ U : UpperSet β, S = σ ⁻¹' U

/-- A set is contiguous on a scale when it is the preimage of an order-connected set. -/
def Contiguous (σ : α → β) (S : Set α) : Prop := ∃ I : Set β, I.OrdConnected ∧ S = σ ⁻¹' I

/-- A scale `τ` coarsens a scale `σ` when it preserves its order. -/
def Coarsens (τ : α → γ) (σ : α → β) : Prop := ∀ a b, σ a ≤ σ b → τ a ≤ τ b

/-- Whether sonority rises (`lt`), plateaus (`eq`) or falls (`gt`) from `a` to `b`. -/
def profile (σ : α → β) (a b : α) : Ordering := compare (σ a) (σ b)

theorem IsCut.total (hS : IsCut σ S) (hT : IsCut σ T) : S ⊆ T ∨ T ⊆ S := by
  obtain ⟨U, rfl⟩ := hS
  obtain ⟨V, rfl⟩ := hT
  exact (le_total V U).imp (Set.preimage_mono ·) (Set.preimage_mono ·)

theorem not_isCut_and_isCut (hST : ¬ S ⊆ T) (hTS : ¬ T ⊆ S) : ¬ (IsCut σ S ∧ IsCut σ T) :=
  fun ⟨hS, hT⟩ ↦ (hS.total hT).elim hST hTS

theorem IsCut.contiguous (h : IsCut σ S) : Contiguous σ S := by
  obtain ⟨U, rfl⟩ := h
  exact ⟨U, U.upper.ordConnected, rfl⟩

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
  obtain ⟨U, rfl⟩ := hS
  refine ⟨⟨{y | ∃ a ∈ τ ⁻¹' U, σ a ≤ y}, fun x y hxy ⟨a, ha, hax⟩ ↦ ⟨a, ha, hax.trans hxy⟩⟩, ?_⟩
  ext b
  exact ⟨fun hb ↦ ⟨b, hb, le_rfl⟩, fun ⟨a, ha, hab⟩ ↦ U.upper (h a b hab) ha⟩

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

theorem rank_strictMono : StrictMono rank := fun _ _ h ↦ h

/-- [sonorant], [approximant], [consonantal] and [syllabic] cut the hierarchy (Table 4.1). -/
theorem isCut_features :
    IsCut id {c : Sonority | c.toSegment.HasValue .sonorant true} ∧
      IsCut id {c : Sonority | c.toSegment.HasValue .approximant true} ∧
      IsCut id {c : Sonority | c.toSegment.HasValue .consonantal false} ∧
      IsCut id {c : Sonority | c.toSegment.HasValue .syllabic true} := by
  refine ⟨⟨.Ici nasal, ?_⟩, ⟨.Ici liquid, ?_⟩, ⟨.Ici glide, ?_⟩, ⟨.Ici vowel, ?_⟩⟩ <;>
  · ext c
    simp only [Set.mem_preimage, id, UpperSet.coe_Ici, Set.mem_Ici]
    cases c <;> decide

/-- The features `ofSegment` reads, the four of Table 4.1. -/
def features : Finset Feature := {.sonorant, .approximant, .consonantal, .syllabic}

theorem ofSegment_congr {s s' : Segment} (h : ∀ f ∈ features, s f = s' f) :
    ofSegment s = ofSegment s' := by
  simp only [ofSegment, Segment.HasValue, h _ (by decide : Feature.sonorant ∈ features),
    h _ (by decide : Feature.approximant ∈ features),
    h _ (by decide : Feature.consonantal ∈ features),
    h _ (by decide : Feature.syllabic ∈ features)]

theorem ofSegment_setFeature {f : Feature} (hf : f ∉ features) (s : Segment) (v : Bool) :
    ofSegment (s.setFeature f v) = ofSegment s :=
  ofSegment_congr fun g hg ↦ Segment.setFeature_apply_of_ne (s := s) (by rintro rfl; exact hf hg) v

@[simp] theorem ofSegment_toSegment (c : Sonority) : ofSegment c.toSegment = c := by
  cases c <;> decide

theorem apply_eq_toSegment_of_le {c : Sonority} {s : Segment} (h : c.toSegment ≤ s) {f : Feature}
    (hf : f ∈ features) : s f = c.toSegment f := by
  have key : ∀ c : Sonority, ∀ f ∈ features, ∃ v, c.toSegment f = some v := by decide
  obtain ⟨v, hv⟩ := key c f hf
  rw [hv]
  exact (Segment.le_iff_forall_hasValue s).1 h f v hv

/-- A segment with the values of a column of Table 4.1 has that column's sonority. -/
theorem ofSegment_eq_of_le {c : Sonority} {s : Segment} (h : c.toSegment ≤ s) :
    ofSegment s = c :=
  (ofSegment_congr fun _ hf ↦ apply_eq_toSegment_of_le h hf).trans (ofSegment_toSegment c)

/-- On a segment with the values of a column of Table 4.1, exactly that column's description
holds. -/
theorem description_le_iff {c c' : Sonority} {s : Segment} (h : c.toSegment ≤ s) :
    c'.description ≤ s ↔ c' = c := by
  have hsupp : ∀ c' : Sonority, ∀ f ∉ features, c'.description f = ⊥ := by decide
  have key : ∀ c c' : Sonority, c'.description ≤ c.toSegment ↔ c' = c := by decide
  rw [← key c c']
  refine forall_congr' fun f ↦ ?_
  by_cases hf : f ∈ features
  · rw [apply_eq_toSegment_of_le h hf]
  · simp [hsupp c' f hf]

theorem description_le_iff_ofSegment_eq {c c' : Sonority} {s : Segment} (h : c.toSegment ≤ s) :
    c'.description ≤ s ↔ ofSegment s = c' := by
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
theorem not_contiguous_continuant :
    ¬ Contiguous ofSegment {s : Segment | s.HasValue .continuant true} := by
  intro h
  exact absurd (contiguous_iff.1 h (.ofSpecs [(.sonorant, false), (.continuant, true)]) (by decide)
    (.ofSpecs [(.syllabic, true), (.sonorant, true), (.approximant, true), (.continuant, true)])
    (by decide) (.ofSpecs [(.sonorant, true), (.approximant, false), (.continuant, false)])
    (by decide) (by decide)) (by decide)

theorem naturalClass_description (c : Sonority) :
    c.description.naturalClass (Finset.univ.image Sonority.toSegment) = {c.toSegment} := by
  revert c
  decide +kernel

/-- Among the columns of Table 4.1, the natural classes are the contiguous sets (p. 76). -/
theorem isNaturalClass_image_iff {S : Finset Sonority} (hS : S.Nonempty) :
    IsNaturalClass (Finset.univ.image Sonority.toSegment) (S.image Sonority.toSegment) ↔
      (S : Set Sonority).OrdConnected := by
  simp only [Set.ordConnected_iff, Finset.mem_coe, Set.subset_def, Set.mem_Icc]
  have key : ∀ S : Finset Sonority, S.Nonempty →
      (IsNaturalClass (Finset.univ.image toSegment) (S.image toSegment) ↔
        ∀ a ∈ S, ∀ b ∈ S, a ≤ b → ∀ c, a ≤ c ∧ c ≤ b → c ∈ S) := by
    decide +kernel
  exact key S hS

open Data.PHOIBLE.FeatureMatrix in
/-- Chart segments fall into the sonority classes of their glyphs, the nasal by its
[−approximant]. -/
example : [«p», «s», «n», «l», «j», «a»].map (ofSegment ∘ Data.PHOIBLE.FeatureMatrix.toSegment) =
    [.obstruent, .obstruent, .nasal, .liquid, .glide, .vowel] := by decide

end Sonority

namespace Segment

variable (s : Segment)

theorem isVowel_iff_le : s.IsVowel ↔ Sonority.vowel.description ≤ s := by
  rw [Sonority.description, ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsVowel]

theorem isObstruent_iff_le : s.IsObstruent ↔ Sonority.obstruent.description ≤ s := by
  rw [Sonority.description, ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsObstruent]

theorem isNasal_iff_le : s.IsNasal ↔ Sonority.nasal.description ≤ s := by
  rw [Sonority.description, ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsNasal]

end Segment

end Phonology
