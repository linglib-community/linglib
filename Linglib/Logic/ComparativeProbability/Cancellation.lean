module

public import Linglib.Logic.ComparativeProbability.Representability
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Cancellation conditions

A pair of event sequences is *balanced* when every state lies in equally many events on each
side. Finite cancellation, Scott's reformulation of the condition of Kraft, Pratt and
Seidenberg, says that when the premise comparisons of a balanced pair hold, the head
comparison holds reversed; it characterizes representability by a single additive measure.

`Scott.lean` proves Scott's theorem in the sign-vector form of the condition and shows the two
forms agree (`ComparativeProbability.cancellation_iff_finiteCancellation`). This file holds the
balanced-sequence form and its soundness: the order a finite measure induces, and so every
representable qualitative probability order, satisfies finite cancellation.

## Main definitions

* `BalancedSeqs`, `FiniteCancellation`: balance and finite cancellation.

## Main statements

* `MeasureTheory.Measure.finiteCancellation`, `Representable.finiteCancellation`: soundness.

## References

* [scott-1964]
* [kraft-pratt-seidenberg-1959]
-/

@[expose] public section

namespace ComparativeProbability

variable {W : Type*}

open scoped Classical in
/-- `seqCount s Es` counts the events of `Es` that contain `s`. -/
noncomputable def seqCount (s : W) (Es : List (Set W)) : ℕ :=
  (Es.map (fun E => if s ∈ E then (1 : ℕ) else 0)).sum

@[simp] theorem seqCount_nil (s : W) : seqCount s [] = 0 := rfl

open scoped Classical in
@[simp] theorem seqCount_cons (s : W) (E : Set W) (Es : List (Set W)) :
    seqCount s (E :: Es) = (if s ∈ E then 1 else 0) + seqCount s Es := by
  simp [seqCount]

/-- Two event sequences are **balanced** when every state lies in equally many events on the
    left as on the right. -/
def BalancedSeqs (Es Fs : List (Set W)) : Prop := ∀ s : W, seqCount s Es = seqCount s Fs

/-- **Finite cancellation** holds when `Y ≿ X` for every balanced pair `⟨…, X⟩` / `⟨…, Y⟩`
    whose premise comparisons all hold. Here `prem` carries the paired premise events and
    `X`, `Y` are the heads. -/
def FiniteCancellation (ge : Set W → Set W → Prop) : Prop :=
  ∀ (prem : List (Set W × Set W)) (X Y : Set W),
    BalancedSeqs (X :: prem.map Prod.fst) (Y :: prem.map Prod.snd) →
    (∀ p ∈ prem, ge p.1 p.2) → ge Y X

/-! ### Measures satisfy finite cancellation -/

section

open MeasureTheory

variable [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] (μ : Measure W)
  [IsFiniteMeasure μ]

open scoped Classical in
private lemma measureReal_eq_sum_ite (E : Set W) :
    μ.real E = ∑ s, if s ∈ E then μ.real {s} else 0 := by
  conv_lhs => rw [show E = ↑(Finset.univ.filter (· ∈ E)) by ext; simp]
  rw [← sum_measureReal_singleton, Finset.sum_filter]

private lemma measureReal_listSum (L : List (Set W)) :
    (L.map μ.real).sum = ∑ s, μ.real {s} * (seqCount s L : ℝ) := by
  classical
  induction L with
  | nil => simp [seqCount]
  | cons E L ih =>
    rw [List.map_cons, List.sum_cons, ih, measureReal_eq_sum_ite μ E, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [seqCount_cons]; push_cast
    by_cases hs : s ∈ E
    · simp only [hs, ite_true]; ring
    · simp [hs]

private lemma measureReal_listSum_eq_of_balanced {L₁ L₂ : List (Set W)} (h : BalancedSeqs L₁ L₂) :
    (L₁.map μ.real).sum = (L₂.map μ.real).sum := by
  rw [measureReal_listSum μ L₁, measureReal_listSum μ L₂]
  exact Finset.sum_congr rfl fun s _ ↦ by rw [h s]

omit [Fintype W] [MeasurableSingletonClass W] in
private lemma measureReal_sum_mono {prem : List (Set W × Set W)}
    (hprem : ∀ p ∈ prem, μ.inducedGe p.1 p.2) :
    ((prem.map Prod.snd).map μ.real).sum ≤ ((prem.map Prod.fst).map μ.real).sum := by
  induction prem with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add ((μ.inducedGe_iff_real).1 (hprem p (List.mem_cons_self ..)))
      (ih fun q hq ↦ hprem q (List.mem_cons_of_mem _ hq))

/-- The order a finite measure induces satisfies finite cancellation, since a balanced pair of
    sequences has equal total measure on its two sides. -/
theorem _root_.MeasureTheory.Measure.finiteCancellation : FiniteCancellation μ.inducedGe := by
  intro prem X Y hbal hprem
  have hsum := measureReal_listSum_eq_of_balanced μ hbal
  simp only [List.map_cons, List.sum_cons] at hsum
  rw [μ.inducedGe_iff_real]
  linarith [measureReal_sum_mono μ hprem]

end

/-- A representable relation satisfies finite cancellation (the soundness half of Scott's
    theorem, in balanced-sequence form). -/
theorem Representable.finiteCancellation [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] {r : Set W → Set W → Prop} (h : Representable r) :
    FiniteCancellation r := by
  obtain ⟨μ, hμ, hm⟩ := h
  intro prem X Y hbal hprem
  exact (hm Y X).mpr (μ.finiteCancellation prem X Y hbal fun p hp ↦ (hm p.1 p.2).mp (hprem p hp))

end ComparativeProbability
