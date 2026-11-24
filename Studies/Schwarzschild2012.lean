module

public import Linglib.Semantics.Events.Path
public import Mathlib.Algebra.Order.Group.Abs
public import Studies.Stassen1985

/-!
# Schwarzschild (2012): Directed scale segments

This file defines directed scale segments and the denotations Schwarzschild gives to a
comparative whose standard is marked by a spatial adposition.

A *directed scale segment* is a part of a scale with a start and an end. It is *rising* if its
start is lower on the scale than its end, and *falling* if it is higher. Hindi *se* 'from' with
the standard `x` says that some rising segment starts at `x`. A gradable predicate with the
measure `μ` says that the segment ends at its subject `y` and lies on the scale of `μ`. So
*Anu Raj-se lambii hai* 'Anu is taller than Raj' holds if and only if `μ x < μ y`.

Hindi *kam* 'less' inverts the scale of the predicate, and Navajo *-'oh* takes falling
segments. We prove that both say `μ y < μ x`. A segment is also a two-point path of entities.
We prove that a rising segment starts at `x` if and only if it is a coinitial path relative
to `{x}`, as a spatial path from a place is.

## Implementation notes

A scale is its measure, a function from entities to a linearly ordered group. The inverse of a
scale is the negated measure, which keeps the distances and reverses the order.

The standard phrases are quantifiers over segments, as in the paper, and are applied to the
predicate saturated by its subject. The paper leaves the mode of combination open.

## TODO

* The positive form, the Navajo comparative built on it, and gradable predicates with more
  than one individual argument are not formalized.
* There are no rows. The Navajo examples are Bogal-Allbritten's, whose work is not in the
  bibliography.

## References

* [R. Schwarzschild, *Directed scale segments* (2012)][schwarzschild-2012]
* [L. Stassen, *Comparison and Universal Grammar* (1985)][stassen-1985]
* [J. Zwarts, *Prepositional aspect and the algebra of paths* (2005)][zwarts-2005]
-/

@[expose] public section

namespace Schwarzschild2012

open Spatial Spatial.Path

/-- (5): A directed scale segment, with the measure of its scale. -/
structure Segment (E D : Type*) where
  /-- The start of the segment. -/
  start : E
  /-- The end of the segment. -/
  finish : E
  /-- The measure of the scale the segment is a part of. -/
  scale : E → D

namespace Segment

variable {E D : Type*}

/-- The segment run from its end to its start. -/
def reverse (σ : Segment E D) : Segment E D := ⟨σ.finish, σ.start, σ.scale⟩

@[simp] theorem reverse_reverse (σ : Segment E D) : σ.reverse.reverse = σ := rfl

/-- The segment as a path of entities from its start to its end. -/
def toPath (σ : Segment E D) : Path E := Path.ofPoints σ.start [σ.finish]

@[simp] theorem head_toPath (σ : Segment E D) : σ.toPath.head = σ.start := rfl

@[simp] theorem last_toPath (σ : Segment E D) : σ.toPath.last = σ.finish := rfl

/-- A segment with distinct ends is a coinitial path relative to an entity exactly when it
starts at it. -/
theorem isCoinitial_toPath_iff {σ : Segment E D} {x : E} (h : σ.start ≠ σ.finish) :
    IsCoinitial {x} σ.toPath ↔ σ.start = x := by
  refine ⟨fun hc ↦ by simpa using hc.2.1, fun hx ↦ ⟨fun i j hji hi ↦ ?_, by simpa using hx, ?_⟩⟩
  · have key : ∀ i : Fin (σ.toPath.length + 1), i ≠ ⊥ → i = ⊤ :=
      (by decide : ∀ i : Fin 2, i ≠ ⊥ → i = ⊤)
    have hi0 : i = ⊥ := by
      by_contra hne
      have hi' : σ.toPath i = x := hi
      rw [key i hne, coe_top, last_toPath] at hi'
      exact h (hx.trans hi'.symm)
    obtain rfl : j = ⊥ := le_bot_iff.mp (hi0 ▸ hji)
    exact hi0 ▸ hi
  · simpa using fun he : σ.finish = x ↦ h (hx.trans he.symm)

section LinearOrder

variable [LinearOrder D] (σ : Segment E D)

/-- (5): A segment is rising when its start is lower on its scale than its end. -/
def Rising : Prop := σ.scale σ.start < σ.scale σ.finish

/-- (5): A segment is falling when its end is lower on its scale than its start. -/
def Falling : Prop := σ.scale σ.finish < σ.scale σ.start

@[simp] theorem rising_reverse : σ.reverse.Rising ↔ σ.Falling := .rfl

@[simp] theorem falling_reverse : σ.reverse.Falling ↔ σ.Rising := .rfl

variable {σ}

theorem Rising.start_ne_finish (h : σ.Rising) : σ.start ≠ σ.finish :=
  fun he ↦ h.ne (congrArg σ.scale he)

end LinearOrder

section Group

variable [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] (σ : Segment E D)

/-- (22): The segment on the inverse scale, with the same distances and the order reversed. -/
def inverse : Segment E D := ⟨σ.start, σ.finish, -σ.scale⟩

@[simp] theorem rising_inverse : σ.inverse.Rising ↔ σ.Falling := by
  simp [inverse, Rising, Falling]

@[simp] theorem falling_inverse : σ.inverse.Falling ↔ σ.Rising := by
  simp [inverse, Rising, Falling]

/-- The length of a segment, the distance on its scale between its start and its end. -/
def length : D := |σ.scale σ.finish - σ.scale σ.start|

end Group

end Segment

open Segment

variable {E D : Type*}

/-! ### The denotations -/

section LinearOrder

variable [LinearOrder D] {μ : E → D} {x y : E}

/-- (23): Hindi *se* 'from' with the standard `x`: some rising segment starts at `x` and
satisfies the predicate. -/
def se (x : E) (P : Segment E D → Prop) : Prop := ∃ σ, σ.Rising ∧ σ.start = x ∧ P σ

/-- (26): Navajo *-'oh* with the standard `x`: some falling segment starts at `x` and satisfies
the predicate. -/
def oh (x : E) (P : Segment E D → Prop) : Prop := ∃ σ, σ.Falling ∧ σ.start = x ∧ P σ

/-- (8): A gradable predicate with the measure `μ` holds of a segment and an individual when the
segment ends at the individual and is a part of the scale of `μ`. -/
def gradable (μ : E → D) (σ : Segment E D) (x : E) : Prop := σ.finish = x ∧ σ.scale = μ

/-- (9): The *se*-comparative says that the subject is above the standard. -/
theorem se_gradable_iff : se x (gradable μ · y) ↔ μ x < μ y :=
  ⟨by rintro ⟨σ, hr, rfl, rfl, rfl⟩; exact hr, fun h ↦ ⟨⟨x, y, μ⟩, h, rfl, rfl, rfl⟩⟩

-- (25): The comparative with *-'oh* says that the subject is below the standard.
theorem oh_gradable_iff : oh x (gradable μ · y) ↔ μ y < μ x :=
  ⟨by rintro ⟨σ, hf, rfl, rfl, rfl⟩; exact hf, fun h ↦ ⟨⟨x, y, μ⟩, h, rfl, rfl, rfl⟩⟩

/-- The segment of a *se*-comparative is a coinitial path relative to the standard. -/
theorem se_iff_isCoinitial {P : Segment E D → Prop} :
    se x P ↔ ∃ σ, σ.Rising ∧ IsCoinitial {x} σ.toPath ∧ P σ :=
  exists_congr fun _ ↦ and_congr_right fun hr ↦
    and_congr_left' (isCoinitial_toPath_iff hr.start_ne_finish).symm

end LinearOrder

section Group

variable [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] {μ : E → D} {x y : E} {d : D}

/-- (11): A differential measure phrase restricts a gradable predicate to the segments of its
length. -/
def differential (d : D) (R : Segment E D → E → Prop) (σ : Segment E D) (x : E) : Prop :=
  R σ x ∧ σ.length = d

/-- (21): Hindi *kam* 'less' holds of a segment that ends at the individual and lies on the
inverse of the scale of a segment the predicate holds of. -/
def kam (R : Segment E D → E → Prop) (σ : Segment E D) (x : E) : Prop :=
  σ.finish = x ∧ ∃ σ', R σ' x ∧ σ.scale = -σ'.scale

-- (13): With a differential, the subject is above the standard by the measure.
theorem se_differential_iff :
    se x (differential d (gradable μ) · y) ↔ μ x < μ y ∧ μ y - μ x = d := by
  constructor
  · rintro ⟨σ, hr, rfl, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨hr, (abs_of_pos (sub_pos.mpr hr)).symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨⟨x, y, μ⟩, h, rfl, ⟨rfl, rfl⟩, abs_of_pos (sub_pos.mpr h)⟩

-- (20): The *se*-comparative with *kam* says that the subject is below the standard.
theorem se_kam_iff : se x (kam (gradable μ) · y) ↔ μ y < μ x := by
  constructor
  · rintro ⟨σ, hr, rfl, rfl, σ', ⟨-, rfl⟩, hs⟩
    simpa [Rising, hs] using hr
  · exact fun h ↦ ⟨⟨x, y, -μ⟩, by simpa [Rising] using h, rfl, rfl, ⟨y, y, μ⟩, ⟨rfl, rfl⟩, rfl⟩

/-- Inverting the scale of the predicate, as Hindi *kam* does, and quantifying over falling
segments, as Navajo *-'oh* does, give the same truth conditions. -/
theorem se_kam_iff_oh : se x (kam (gradable μ) · y) ↔ oh x (gradable μ · y) :=
  se_kam_iff.trans oh_gradable_iff.symm

end Group

/-! ### The fragment -/

/-- The segment of a *se*-comparative has, relative to the standard, the shape of the case the
fragment gives the standard of the Hindi-Urdu construction, and the type of the construction in
Stassen's typology is the adverbial type of the direction of that shape. -/
theorem se_shape {β : Type*} [LinearOrder D] [Preorder β] (near : E → β) :
    ∀ k ∈ HindiUrdu.Comparison.se.standard.case?, ∀ s ∈ k.shape?,
      (∀ (σ : Segment E D) (x : E), σ.Rising → σ.start = x → HasShape {x} σ.toPath near s) ∧
        Stassen1985.typeOf HindiUrdu.Comparison.se =
          (Stassen1985.groundOrder? s.direction).map .adverbial := by
  intro k hk s hs
  obtain rfl : k = .abl := by
    simpa [HindiUrdu.Comparison.se, Comparative.Standard.case?] using hk.symm
  obtain rfl : s = .coinitial := by simpa [Case.shape?] using hs.symm
  exact ⟨fun σ x hr hx ↦ (isCoinitial_toPath_iff hr.start_ne_finish).mpr hx, by decide⟩

end Schwarzschild2012
