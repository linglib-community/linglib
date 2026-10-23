module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Communicative efficiency

This file defines the scalarization of a pair of communicative costs by a tradeoff parameter and
the deviation of an attested encoding from the efficient frontier.

Many linguistic phenomena arise from a tension between two functional pressures, and attested
forms tend to be efficient compromises between them. A `CostPair` records the two costs. In the
work of Xu and colleagues they are speaker effort, measured by word length, and information loss,
measured by listener surprisal. For Kemp and Regier they are complexity and loss of
informativeness, and for Zaslavsky and colleagues they are the complexity `I(W;U)` and the
distortion `D[p‖q]` of an information bottleneck. The weighted cost `L_β = cost₂ + β · cost₁`
trades one against the other, and the efficiency loss of an attested pair is its least deviation,
over a list of values of `β`, from the pair that is optimal at that `β`.

## Main definitions

* `CostPair`: a pair of costs, such as effort and information loss.
* `weightedCost`: the linear scalarization `L_β = cost₂ + β · cost₁`.
* `efficiencyLossAt`: the deviation from the optimal pair at one `β`.
* `efficiencyLoss`: the least deviation across a list of values of `β`.

## Main results

* `frontier_antitone`: optimal pairs move along the frontier as `β` grows, with smaller `cost₁`
  and larger `cost₂`.
* `efficiencyLoss_nonneg`: the efficiency loss against optimal pairs is nonnegative.

## References

* [A. Xu, C. Kemp, L. Frermann and Y. Xu, *Word reuse and combination support efficient
  communication of emerging concepts* (2024)][xu-etal-2024]
* [C. Kemp and T. Regier, *Kinship categories across languages reflect general communicative
  principles* (2012)][kemp-regier-2012]
* [N. Zaslavsky, C. Kemp, T. Regier and N. Tishby, *Efficient compression in color naming and its
  evolution* (2018)][zaslavsky-kemp-regier-tishby-2018]
-/

@[expose] public section

namespace Pragmatics.Efficiency

/-- A pair of communicative costs, which can stand for any two pressures in a functional tradeoff.
-/
structure CostPair where
  cost₁ : ℝ
  cost₂ : ℝ

/-- The weighted cost is the linear scalarization `L_β = cost₂ + β · cost₁` of the two costs. At `β
= 0` only `cost₂` counts, and a large `β` emphasizes `cost₁`. -/
def weightedCost (c : CostPair) (β : ℝ) : ℝ :=
  c.cost₂ + β * c.cost₁

/-- The efficiency loss at `β` is the deviation of the attested pair from the optimal one. -/
def efficiencyLossAt (attested optimal : CostPair) (β : ℝ) : ℝ :=
  weightedCost attested β - weightedCost optimal β

/-- The overall efficiency loss is the least deviation across the listed values of `β`, `ε = min_β
(L_β[attested] − L_β[optimal_β])`. -/
noncomputable def efficiencyLoss (attested : CostPair) (optimalAt : ℝ → CostPair)
    (βs : List ℝ) : ℝ :=
  match βs.map (fun β ↦ efficiencyLossAt attested (optimalAt β) β) with
  | [] => 0
  | x :: xs => xs.foldl min x

@[simp] theorem efficiencyLossAt_self (c : CostPair) (β : ℝ) :
    efficiencyLossAt c c β = 0 := by
  simp [efficiencyLossAt]

theorem weightedCost_mono_β (c : CostPair) {β₁ β₂ : ℝ}
    (hβ : β₁ ≤ β₂) (hc : 0 ≤ c.cost₁) :
    weightedCost c β₁ ≤ weightedCost c β₂ :=
  add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hβ hc)

theorem frontier_antitone {a b : CostPair} {β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ : β₁ < β₂)
    (h₁ : weightedCost a β₁ ≤ weightedCost b β₁)
    (h₂ : weightedCost b β₂ ≤ weightedCost a β₂) :
    b.cost₁ ≤ a.cost₁ ∧ a.cost₂ ≤ b.cost₂ := by
  unfold weightedCost at h₁ h₂
  have hb : b.cost₁ ≤ a.cost₁ := by
    by_contra hc
    nlinarith [mul_pos (sub_pos.2 hβ) (sub_pos.2 (not_le.mp hc))]
  exact ⟨hb, by nlinarith [mul_nonneg hβ₁ (sub_nonneg.2 hb)]⟩

theorem efficiencyLossAt_nonneg {attested optimal : CostPair} {β : ℝ}
    (h : weightedCost optimal β ≤ weightedCost attested β) :
    0 ≤ efficiencyLossAt attested optimal β :=
  sub_nonneg.2 h

theorem efficiencyLoss_nonneg {attested : CostPair} {optimalAt : ℝ → CostPair} {βs : List ℝ}
    (h : ∀ β ∈ βs, weightedCost (optimalAt β) β ≤ weightedCost attested β) :
    0 ≤ efficiencyLoss attested optimalAt βs := by
  unfold efficiencyLoss
  have key : ∀ (l : List ℝ) (x : ℝ), 0 ≤ x → (∀ y ∈ l, 0 ≤ y) → 0 ≤ l.foldl min x := by
    intro l
    induction l with
    | nil => intro x hx _; simpa using hx
    | cons y ys ih =>
      intro x hx hl
      exact ih _ (le_min hx (hl y (List.mem_cons_self ..)))
        fun z hz ↦ hl z (List.mem_cons_of_mem _ hz)
  cases hβs : βs.map fun β ↦ efficiencyLossAt attested (optimalAt β) β with
  | nil => exact le_rfl
  | cons x xs =>
    have hall : ∀ y ∈ x :: xs, 0 ≤ y := by
      rw [← hβs]
      simp only [List.mem_map, forall_exists_index, and_imp]
      rintro y β hβ rfl
      exact efficiencyLossAt_nonneg (h β hβ)
    exact key xs x (hall x (List.mem_cons_self ..))
      fun z hz ↦ hall z (List.mem_cons_of_mem _ hz)

end Pragmatics.Efficiency
