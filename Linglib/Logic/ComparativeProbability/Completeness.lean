module

public import Linglib.Logic.ComparativeProbability.CancellationFin4
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.FinCases

/-! # Representation theorems for qualitative probability

This file defines Kraft, Pratt and Seidenberg's order on the subsets of five atoms and proves the
representation theorems for qualitative probabilities on a finite set. Below five atoms every
qualitative probability is induced by a probability measure. The Kraft–Pratt–Seidenberg order
satisfies de Finetti's axioms but no probability measure induces it, and adding null atoms
carries it to every larger set. Every qualitative probability on a finite set is induced by a
qualitatively additive measure.

## Main statements

* `ComparativeProbability.kps_not_representable`: the Kraft–Pratt–Seidenberg order is not
  representable.
* `ComparativeProbability.representable_of_card_lt_five`: below five atoms every qualitative
  probability is representable.
* `ComparativeProbability.exists_not_representable_of_five_le_card`: from five atoms on, some
  qualitative probability is not representable.
* `ComparativeProbability.exists_qualAddMeasure_repr`: every qualitative probability on a finite
  set is induced by a qualitatively additive measure.

## References

* [kraft-pratt-seidenberg-1959]
* [holliday-icard-2013]
-/

@[expose] public section

open MeasureTheory

namespace ComparativeProbability

/-! ### The Kraft–Pratt–Seidenberg order -/

/-- `kpsOrder` lists the subsets of the atoms `p, q, r, s, t`, numbered `0, …, 4`, from least to
    most likely in Kraft, Pratt and Seidenberg's counterexample (p. 415). The less likely half is
    `∅ < q < r < s < qr < qs < p < pq < rs < t < qrs < rp < ps < tq < qrp < rt`; the more likely
    half is their complements in reverse order, as in any additive simple ordering
    (Proposition 1, p. 414). -/
def kpsOrder : List (Finset (Fin 5)) :=
  let lower : List (Finset (Fin 5)) := [∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {0}, {0, 1}, {2, 3},
    {4}, {1, 2, 3}, {0, 2}, {0, 3}, {1, 4}, {0, 1, 2}, {2, 4}]
  lower ++ (lower.map (·ᶜ)).reverse

/-- `kpsRank s` is the position of `s` in the Kraft–Pratt–Seidenberg order. -/
def kpsRank (s : Finset (Fin 5)) : ℕ := kpsOrder.idxOf s

private theorem kpsRank_qadd : ∀ a b : Finset (Fin 5),
    kpsRank b ≤ kpsRank a ↔ kpsRank (b \ a) ≤ kpsRank (a \ b) := by
  decide

section KPS

open scoped Classical

/-- `kpsGe A B` holds when `A` comes no earlier than `B` in the Kraft–Pratt–Seidenberg order. -/
noncomputable def kpsGe (A B : Set (Fin 5)) : Prop := kpsRank B.toFinset ≤ kpsRank A.toFinset

/-- The Kraft–Pratt–Seidenberg order is a qualitative probability. -/
instance : IsQualitativeProbability kpsGe where
  trans _ _ _ hab hbc := hbc.trans hab
  total A B := le_total _ _
  rel_bot' _ := by
    simp only [kpsGe, Set.bot_eq_empty, Set.toFinset_empty]
    exact (show kpsRank ∅ = 0 by decide).trans_le (Nat.zero_le _)
  qadd A B := by simp only [kpsGe, Set.toFinset_sdiff]; exact kpsRank_qadd _ _
  bot_not_ge_top := by simp only [kpsGe, Set.bot_eq_empty, Set.top_eq_univ, Set.toFinset_empty,
    Set.toFinset_univ]; decide

@[simp] theorem kpsGe_coe (A B : Finset (Fin 5)) : kpsGe ↑A ↑B ↔ kpsRank B ≤ kpsRank A := by
  simp only [kpsGe, Finset.toFinset_coe]

/-- **The Kraft–Pratt–Seidenberg order is not representable.** It makes the comparisons
    `p ≻ qs`, `pqs ≻ rt`, `rs ≻ pq` and `qt ≻ ps` strict, yet each atom lies on as many of their
    left sides as right sides, which no probability measure allows (p. 414). -/
theorem kps_not_representable : ¬Representable kpsGe := by
  rintro ⟨μ, _, hμ⟩
  let A : Fin 4 → Finset (Fin 5) := ![{0}, {0, 1, 3}, {2, 3}, {1, 4}]
  let B : Fin 4 → Finset (Fin 5) := ![{1, 3}, {2, 4}, {0, 1}, {0, 3}]
  have hlt (i : Fin 4) : AsymmRel μ.inducedGe (A i) (B i) := by
    rw [hμ, AsymmRel, kpsGe_coe, kpsGe_coe]; fin_cases i <;> decide
  refine μ.not_asymmRel_of_balanced (A := fun i ↦ A i) (B := fun i ↦ B i) (fun s ↦ ?_)
    (fun i ↦ (hlt i).1) 0 (hlt 0)
  simp only [Set.indicator_apply, Finset.mem_coe]; revert s; decide

end KPS

/-! ### The Kraft–Pratt–Seidenberg theorems -/

/-- **Below five atoms.** Every qualitative probability on fewer than five atoms is
    representable, since it satisfies Scott cancellation. -/
theorem representable_of_card_lt_five {W : Type*} [Fintype W] [MeasurableSpace W]
    [DiscreteMeasurableSpace W] (r : Set W → Set W → Prop) [IsQualitativeProbability r]
    (hcard : Fintype.card W < 5) : Representable r :=
  (cancellation_implies_representable _
    (cancellation_of_le_four (n := Fintype.card W) (by omega) _)).of_preimage
    (Fintype.equivFin W).injective

/-- **From five atoms on.** Some qualitative probability on the set is not representable: the
    Kraft–Pratt–Seidenberg order on five of its atoms, with the others null. -/
theorem exists_not_representable_of_five_le_card {W : Type*} [Fintype W] [MeasurableSpace W]
    [DiscreteMeasurableSpace W] (hcard : 5 ≤ Fintype.card W) :
    ∃ r : Set W → Set W → Prop, IsQualitativeProbability r ∧ ¬Representable r := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 5) (by simpa using hcard)
  exact ⟨Set.preimage f ⁻¹'o kpsGe, inferInstance, fun h ↦
    kps_not_representable (h.of_preimage f.injective)⟩

/-! ### Qualitatively additive representation -/

section Repr

variable {W : Type*} [Finite W] (r : Set W → Set W → Prop) [IsQualitativeProbability r]

/-- Counting the sets strictly less likely than a set ranks the sets as `r` does. -/
private theorem ncard_lt_le_ncard_lt_iff (A B : Set W) :
    {S | AsymmRel r B S}.ncard ≤ {S | AsymmRel r A S}.ncard ↔ r A B := by
  refine ⟨fun h ↦ by_contra fun hAB ↦ h.not_gt (Set.ncard_lt_ncard ?_), fun hAB ↦
    Set.ncard_le_ncard fun S hS ↦ asymmRel_of_rel_of_asymmRel hAB hS⟩
  have hBA : AsymmRel r B A := ⟨(total_of r A B).resolve_left hAB, hAB⟩
  exact ⟨fun S hS ↦ asymmRel_of_rel_of_asymmRel hBA.1 hS, fun h ↦ (h hBA).2 (refl_of r A)⟩

/-- **Qualitatively additive representation.** Every qualitative probability on a finite set is
    induced by a qualitatively additive measure: the number of sets strictly less likely than a
    set, divided by the number strictly less likely than the whole space. Holliday and Icard's
    logic FA is complete over these measures (Theorem 6, p. 523). -/
theorem exists_qualAddMeasure_repr : ∃ m : QualAddMeasure ℚ W, m.inducedGe = r := by
  let g : Set W → ℚ := fun A ↦ {S | AsymmRel r A S}.ncard
  have hg (A B : Set W) : r A B ↔ g B ≤ g A := by
    rw [Nat.cast_le, ncard_lt_le_ncard_lt_iff]
  have h0 : g ∅ = 0 := by simp [g, AsymmRel, rel_empty]
  have hpos : 0 < g Set.univ := h0 ▸ lt_of_not_ge ((hg ∅ Set.univ).not.mp not_rel_empty_univ)
  have hf (A B : Set W) : r A B ↔ g B / g Set.univ ≤ g A / g Set.univ := by
    rw [div_le_div_iff_of_pos_right hpos, hg]
  exact ⟨_, QualAddMeasure.inducedGe_ofRepr _ hf (by simp [h0]) (div_self hpos.ne')⟩

end Repr

end ComparativeProbability
