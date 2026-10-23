module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.Tense.Allen
public import Linglib.Semantics.Tense.Defs

/-!
# Perspectival tense

This file evaluates the comparison cells of `Semantics/Tense/Defs.lean` on time intervals, the
perspectival presuppositions of Tsilia and Zhao. Tenses and temporal deictic adverbs are
temporal pronouns: each denotes a time, an interval of a linear order, and presupposes that it
stands to a temporal perspective `π`, itself an interval, in one of the positions its cell
admits. An interval precedes, overlaps or follows another
(`NonemptyInterval.position`), so PRES, which presupposes overlap with `π`, is the cell
`present`; PAST, which presupposes precedence, is `past`; and the adverb ⌈then⌉, which
presupposes disjointness, is `presentᶜ`. On point intervals the presupposition is the comparison
of the points, which the pronominal tense of `Semantics/Tense/Pronoun.lean` presupposes
(`presup_pure`).

The perspective is an interpretation parameter that an operator rebinds for a whole clause, so a
clausemate tense and adverb read the same `π`, and the adverb restricts the tense: the reference
of the tense lies within that of the adverb. Overlap passes to a containing interval, so an
adverb can restrict a present tense exactly when its cell admits overlap
(`exists_presup_present_iff`). The adverbs whose cell excludes it are the distal ones, and their
clash with the present is the ⌈then⌉-present puzzle.

## Main definitions

* `Tense.DeicticAdverb`: the lexical entry of a temporal deictic adverb, a surface form with the
  cell of positions its reference may occupy relative to its anchor.
* `Tense.DeicticAdverb.IsDistal`: the cell excludes overlap, as for English *then*.
* `Tense.Perspective.Presup`: the presupposition of a temporal pronoun with a given cell,
  relative to a perspective.
* `Tense.Perspective.toSetRel`: a cell as a relation between intervals.

## Main results

* `Tense.Perspective.not_presup_of_presup_present`: a reference overlapping the perspective
  cannot be restricted by a distal adverb.
* `Tense.Perspective.exists_presup_present_iff`: the distal cells are exactly those that cannot
  restrict a present.
* `Tense.Perspective.Presup.mono`: a stronger cell satisfies a weaker one's presupposition, so
  a reference that precedes the perspective is disjoint from it.

## References

* [tsilia-zhao-2026]
* [zhao-2025]
-/

@[expose] public section

namespace Tense

open Semantics
open scoped SetRel

/-- A temporal deictic adverb is a pro-form for a time located relative to an anchor, such as
English *then* and *now*, Greek *tóte*, and Russian *togda* and *sejčas*. The entry records the
positions the adverb's reference may occupy relative to the anchor as a comparison cell; what
the anchor is, the utterance time or a shiftable perspective, is a matter of analysis and is
left to studies. -/
structure DeicticAdverb where
  /-- The surface form. -/
  form : String
  /-- The positions relative to the anchor that the adverb's reference may occupy. -/
  cell : Finset Ordering
  deriving DecidableEq

/-- A distal adverb refers to a time away from its anchor, so its cell excludes overlap. -/
def DeicticAdverb.IsDistal (a : DeicticAdverb) : Prop := .eq ∉ a.cell

instance : DecidablePred DeicticAdverb.IsDistal :=
  fun a ↦ inferInstanceAs (Decidable (.eq ∉ a.cell))

namespace Perspective

variable {T : Type*} [LinearOrder T] {C D : Finset Ordering} {π r th : NonemptyInterval T}

/-- The perspectival presupposition of a temporal pronoun with cell `C` is that its reference
stands to the perspective `π` in one of the positions of `C`. -/
def Presup (C : Finset Ordering) (π ref : NonemptyInterval T) : Prop := ref.position π ∈ C

instance : Decidable (Presup C π r) := inferInstanceAs (Decidable (_ ∈ C))

@[simp] theorem presup_present : Presup ⟦present⟧ π r ↔ r.Overlaps π := by
  simp [Presup, denote_present]

@[simp] theorem presup_past : Presup ⟦past⟧ π r ↔ r.Precedes π := by
  simp [Presup, denote_past]

@[simp] theorem presup_future : Presup ⟦future⟧ π r ↔ π.Precedes r := by
  simp [Presup, denote_future]

@[simp] theorem presup_compl_present : Presup ⟦present⟧ᶜ π r ↔ ¬ r.Overlaps π := by
  simp [Presup, denote_present]

@[simp] theorem presup_top : Presup ⊤ π r := Finset.mem_univ _

@[simp] theorem presup_pure {p t : T} :
    Presup C (NonemptyInterval.pure p) (NonemptyInterval.pure t) ↔ compare t p ∈ C := by
  rw [Presup, NonemptyInterval.position_pure]

theorem Presup.mono (h : Presup C π r) (hCD : C ⊆ D) : Presup D π r := hCD h

/-- The relation of a cell on intervals relates a perspective to the intervals that stand to it
in one of the cell's positions. -/
def toSetRel (C : Finset Ordering) : SetRel (NonemptyInterval T) (NonemptyInterval T) :=
  {x | Presup C x.1 x.2}

@[simp] theorem mem_toSetRel : π ~[toSetRel C] r ↔ Presup C π r := .rfl

instance : Decidable (π ~[toSetRel C] r) := inferInstanceAs (Decidable (Presup C π r))

theorem toSetRel_eq_inv (C : Finset Ordering) :
    (toSetRel C : SetRel (NonemptyInterval T) _) = (Allen.toSetRel (Allen.ofPosition C)).inv := by
  ext ⟨π, r⟩
  simp [Presup]

theorem pure_mem_toSetRel {p t : T} :
    .pure p ~[toSetRel C] .pure t ↔ p ~[Tense.toSetRel C] t := by
  simp

theorem toSetRel_past_comp_self [DenselyOrdered T] :
    (toSetRel ⟦past⟧ ○ toSetRel ⟦past⟧ : SetRel (NonemptyInterval T) (NonemptyInterval T)) =
      toSetRel ⟦past⟧ := by
  ext ⟨π, r⟩
  simp only [SetRel.mem_comp, mem_toSetRel, presup_past]
  exact ⟨fun ⟨_, h₁, h₂⟩ ↦ NonemptyInterval.precedes_trans h₂ h₁,
    fun h ↦ let ⟨u, hu, hu'⟩ := exists_between h; ⟨.pure u, hu', hu⟩⟩

/-! ### Restriction by an adverb -/

theorem eq_mem_of_presup_present (hr : Presup ⟦present⟧ π r) (hle : r ≤ th) (hth : Presup C π th) :
    .eq ∈ C := by
  have h : th.position π = .eq :=
    NonemptyInterval.position_eq_eq_of_le (NonemptyInterval.position_eq_eq.2
      (presup_present.1 hr)) hle
  rwa [Presup, h] at hth

/-- A reference overlapping the perspective cannot be restricted by an adverb whose cell excludes
overlap with it, the ⌈then⌉-present clash. -/
theorem not_presup_of_presup_present (hC : .eq ∉ C) (hr : Presup ⟦present⟧ π r) (hle : r ≤ th) :
    ¬ Presup C π th :=
  fun hth ↦ hC (eq_mem_of_presup_present hr hle hth)

/-- The cells that can restrict a present tense are exactly those that admit overlap. -/
theorem exists_presup_present_iff [Nonempty T] :
    (∃ π r th : NonemptyInterval T, Presup ⟦present⟧ π r ∧ r ≤ th ∧ Presup C π th) ↔ .eq ∈ C := by
  refine ⟨fun ⟨_, _, _, hr, hle, hth⟩ ↦ eq_mem_of_presup_present hr hle hth, fun h ↦ ?_⟩
  obtain ⟨t⟩ := ‹Nonempty T›
  refine ⟨.pure t, .pure t, .pure t, presup_present.2 (NonemptyInterval.overlaps_refl _),
    le_rfl, ?_⟩
  rwa [Presup, NonemptyInterval.position_self]

end Perspective

end Tense
