module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.Tense.Allen
public import Linglib.Semantics.Tense.Defs

/-!
# Perspectival tense

Tenses and temporal deictic adverbs are temporal pronouns: each denotes a time, an interval of a
linear order, and presupposes that it stands to a temporal perspective `π`, itself an interval, in
one of the Allen relations of a cell. A comparison cell `C` of `Semantics/Tense/Defs.lean` gives
the cell `Allen.ofPosition C` of the intervals that precede, overlap or follow `π` as `C` allows;
a present that presupposes containment in `π` instead has the cell `Allen.le`. An adverb restricts
the tense of its clause, whose reference lies within the adverb's, so the presuppositions of a
clause hold together for some perspective exactly when the adverb's cell meets the composite of
containment with the tense's cell. On positions the composite is simple: a time containing the
reference stands where the reference does, or overlaps `π`.

## Main definitions

* `Tense.DeicticAdverb`: the lexical entry of a temporal deictic adverb, a surface form with the
  positions its reference may occupy relative to its anchor.
* `Tense.DeicticAdverb.IsDistal`: the cell excludes overlap, as for English *then*.
* `Tense.Perspective.Restricted`: an adverb restricting a tense, the reference of each standing
  to the perspective in its cell's relation `Allen.toSetRel` and the tense's reference lying
  within the adverb's.

## Main results

* `Tense.Perspective.exists_restricted_iff`: on dense time, an adverb can restrict a tense exactly
  when its cell meets the composite of containment with the tense's cell, and
  `Tense.Perspective.exists_restricted_ofPosition_iff` the same for cells of positions.
* `Tense.Perspective.not_ofPosition_of_overlaps`: a distal adverb cannot restrict a reference
  that overlaps the perspective.

## References

* [tsilia-zhao-2026]
* [anand-toosarvandani-2019]
* [zhao-2025]
* [allen-1983]
-/

@[expose] public section

namespace Tense

open scoped Denotes
open scoped SetRel

/-- A temporal deictic adverb is a pro-form for a time located relative to an anchor, such as
English *then* and *now*, Greek *tóte*, and Russian *togda* and *sejčas*. The entry records the
positions the adverb's reference may occupy relative to the anchor, whose cell on intervals is
`Allen.ofPosition`; what the anchor is, the utterance time or a shiftable perspective, is a
matter of analysis and is left to studies. -/
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

variable {T : Type*} [LinearOrder T] {A B : Finset Allen.Relation} {C : Finset Ordering}
  {π r th : NonemptyInterval T}

/-- An adverb with cell `B` and reference `th` restricts a tense with cell `A` and reference `r`
relative to the perspective `π`: both presuppositions hold and the tense's reference lies within
the adverb's. -/
def Restricted (A B : Finset Allen.Relation) (π r th : NonemptyInterval T) : Prop :=
  π ~[Allen.toSetRel A] r ∧ r ≤ th ∧ π ~[Allen.toSetRel B] th

/-- On dense time, an adverb with cell `B` can restrict a reference with cell `A` for some
perspective exactly when `B` meets the composite of containment with `A`. -/
theorem exists_restricted_iff [DenselyOrdered T] [Nontrivial T] :
    (∃ π r th : NonemptyInterval T, Restricted A B π r th) ↔
      (Allen.comp (Allen.inv Allen.le) A ∩ B).Nonempty := by
  refine ⟨fun ⟨π, r, th, hr, hle, hth⟩ ↦ ⟨_, Finset.mem_inter.2 ⟨Allen.toSetRel_comp_subset
    (show (π, th) ∈ Allen.toSetRel A ○ Allen.toSetRel (Allen.inv Allen.le) from
      ⟨r, hr, by simpa using hle⟩), hth⟩⟩, fun ⟨_, ht⟩ ↦ ?_⟩
  obtain ⟨htA, htB⟩ := Finset.mem_inter.1 ht
  obtain ⟨i, j, k, hle, hA, rfl⟩ := Allen.mem_comp.1 htA
  obtain ⟨f⟩ := Order.embedding_from_countable_to_dense (α := Fin 6) (β := T)
  have hji : Allen.relation j i ∈ Allen.le := by simpa using hle
  refine ⟨k.map f.toOrderHom, j.map f.toOrderHom, i.map f.toOrderHom, ?_, ?_, ?_⟩
  · rwa [Allen.mem_toSetRel, Allen.relation_map]
  · rw [← Allen.relation_mem_le, Allen.relation_map]
    exact hji
  · rwa [Allen.mem_toSetRel, Allen.relation_map]

/-- A time containing a reference that overlaps the perspective cannot stand to it in positions
that exclude overlap, the ⌜then⌝-present clash. -/
theorem not_ofPosition_of_overlaps (hC : .eq ∉ C) (hr : r.Overlaps π) (hle : r ≤ th) :
    ¬ π ~[Allen.toSetRel (Allen.ofPosition C)] th := by
  rwa [Allen.mem_toSetRel_ofPosition, NonemptyInterval.position_eq_eq.2 (hr.mono_left hle)]

/-- An adverb with positions `D` can restrict a reference with positions `C` for some
perspective exactly when `D` admits a position of `C`, or overlap. -/
theorem exists_restricted_ofPosition_iff [Nontrivial T] {D : Finset Ordering} :
    (∃ π r th : NonemptyInterval T,
      Restricted (Allen.ofPosition C) (Allen.ofPosition D) π r th) ↔
        ∃ o ∈ C, o ∈ D ∨ .eq ∈ D := by
  simp only [Restricted, Allen.mem_toSetRel_ofPosition]
  refine ⟨fun ⟨π, r, th, hr, hle, hth⟩ ↦ ⟨_, hr, ?_⟩, fun ⟨o, ho, h⟩ ↦ ?_⟩
  · rcases NonemptyInterval.position_eq_or_eq_eq_of_le (i₂ := π) hle with h | h <;> rw [h] at hth
    exacts [.inl hth, .inr hth]
  obtain ⟨a, b, hab⟩ := exists_pair_lt T
  obtain ⟨x, y, hxy⟩ : ∃ x y : T, compare x y = o := by
    cases o
    exacts [⟨a, b, compare_lt_iff_lt.2 hab⟩, ⟨a, a, compare_eq_iff_eq.2 rfl⟩,
      ⟨b, a, compare_gt_iff_gt.2 hab⟩]
  have hr : (NonemptyInterval.pure x).position (.pure y) ∈ C := by
    rwa [NonemptyInterval.position_pure, hxy]
  rcases h with h | h
  · exact ⟨_, _, _, hr, le_rfl, by rwa [NonemptyInterval.position_pure, hxy]⟩
  refine ⟨.pure y, .pure x, .pure x ⊔ .pure y, hr, le_sup_left, ?_⟩
  rwa [NonemptyInterval.position_eq_eq.2
    (NonemptyInterval.overlaps_symm (NonemptyInterval.overlaps_of_le le_sup_right))]

end Perspective

end Tense
