module

public import Linglib.Data.Examples.BachBrownMarslenWilson1986
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fin.Rev

/-!
# Bach, Brown & Marslen-Wilson (1986): crossed vs nested dependencies

Dutch verb clusters cross their NP–verb dependencies (NP₁ NP₂ NP₃ V₁ V₂ V₃),
German nests them (NP₁ NP₂ NP₃ V₃ V₂ V₁). Matched Dutch and German sentences are
rated equally comprehensible at one level of embedding; from two levels on Dutch
is easier on both ratings and probe accuracy (Tables 1, 3) — yet only the nested
pattern is parsable by a push-down store, so parsing difficulty does not track
stack-parsability ([evers-1975], [bresnan-etal-1982]).

An NP–verb binding is a permutation `σ : Equiv.Perm (Fin n)`: crossed is
`Equiv.refl`, nested is `Fin.revPerm`. `totalIntegrationCost` formalizes the paper's informal
argument that crossed orders integrate each NP into the matrix structure as its
verb arrives while nested orders hold every NP until the cluster ends.

## Main statements

* `totalIntegrationCost_refl`, `totalIntegrationCost_revPerm`: closed forms
  `n(n−1)/2` (crossed) and `n(n−1)` (nested).
* `cost_gap`: the gap equals the whole crossed cost — 1 at two verbs, where the
  experiment finds no difference, 3 and 6 at Levels 3–4, where it does.
* `nonprojective_is_cheaper`: the antitone (stack-parsable) binding is the
  expensive one.

## References

* [bach-brown-marslen-wilson-1986]: Crossed and nested dependencies in German
  and Dutch: A psycholinguistic study. *Language and Cognitive Processes* 1.
* [evers-1975]: The transformational cycle in Dutch and German.
* [bresnan-etal-1982]: Cross-serial dependencies in Dutch.
-/

@[expose] public section

namespace BachBrownMarslenWilson1986

variable {n : ℕ}

/-- NPs matrix-integrated after `k` verbs heard: NP `i` counts iff every verb on
the control chain from its verb `V_{σ i}` up to the matrix verb `V_{σ 0}` has
been heard, i.e. `max (σ 0) (σ i) < k`. -/
def integratedCount (σ : Equiv.Perm (Fin n)) (k : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | m + 1 =>
    let matrix := (σ ⟨0, by omega⟩).val
    (List.range (m + 1)).countP λ i =>
      if hi : i < m + 1 then
        max matrix (σ ⟨i, hi⟩).val < k
      else false

/-- NPs still awaiting matrix-connected integration after `k` verbs. -/
def unintegratedCount (σ : Equiv.Perm (Fin n)) (k : ℕ) : ℕ :=
  n - integratedCount σ k

private theorem countP_dite_lt_range (n k : ℕ) :
    (List.range n).countP (λ i => if _ : i < n then decide (i < k) else false) = min k n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
    simp only [show m < m + 1 from by omega, dite_true]
    have : (List.range m).countP (λ i => if _ : i < m + 1 then decide (i < k) else false) =
           (List.range m).countP (λ i => if _ : i < m then decide (i < k) else false) := by
      apply List.countP_congr; intro i hi; simp only [List.mem_range] at hi
      simp [show i < m from hi, show i < m + 1 from by omega]
    rw [this, ih]; by_cases h : m < k <;> simp [h] <;> omega

theorem integratedCount_refl (k : ℕ) :
    integratedCount (Equiv.refl (Fin n)) k = min k n := by
  cases n with
  | zero => simp [integratedCount]
  | succ m => simp only [integratedCount, Equiv.refl_apply, Fin.val_mk]
              exact countP_dite_lt_range (m + 1) k

private theorem rev_max_eq (m i k : ℕ) (hi : i < m + 1) :
    (max (m + 1 - (0 + 1)) (m + 1 - (i + 1)) < k) ↔ m < k := by omega

theorem integratedCount_revPerm (k : ℕ) :
    integratedCount (Fin.revPerm : Equiv.Perm (Fin n)) k = if k ≥ n then n else 0 := by
  cases n with
  | zero => simp [integratedCount]
  | succ m =>
    simp only [integratedCount, Fin.revPerm_apply, Fin.val_rev]
    by_cases hk : k ≥ m + 1
    · rw [ite_eq_left hk]
      have hall : ∀ i ∈ List.range (m + 1),
          (if _ : i < m + 1 then
            decide (max (m + 1 - (0 + 1)) (m + 1 - (i + 1)) < k) else false) = true := by
        intro i hi; simp only [List.mem_range] at hi
        simp only [show i < m + 1 from hi, dite_true, decide_eq_true_eq]
        rw [rev_max_eq m i k hi]; omega
      have h := List.countP_eq_length.mpr hall
      rw [List.length_range] at h; exact h
    · rw [ite_eq_right hk]
      apply List.countP_eq_zero.mpr
      intro i hi; simp only [List.mem_range] at hi
      simp only [show i < m + 1 from hi, dite_true, decide_eq_true_eq]
      rw [rev_max_eq m i k hi]; omega

theorem unintegratedCount_refl (k : ℕ) :
    unintegratedCount (Equiv.refl (Fin n)) k = n - min k n := by
  simp [unintegratedCount, integratedCount_refl]

theorem unintegratedCount_revPerm (k : ℕ) :
    unintegratedCount (Fin.revPerm : Equiv.Perm (Fin n)) k = if k ≥ n then 0 else n := by
  simp only [unintegratedCount, integratedCount_revPerm]; split <;> omega

/-- Cumulative unintegrated NPs across the cluster. -/
def totalIntegrationCost (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ k ∈ Finset.range n, unintegratedCount σ (k + 1)

/-- The crossed (Dutch) cluster costs `n(n−1)/2`: one NP integrates per verb. -/
theorem totalIntegrationCost_refl (n : ℕ) :
    totalIntegrationCost (Equiv.refl (Fin n)) = n * (n - 1) / 2 := by
  unfold totalIntegrationCost
  have h : ∀ k ∈ Finset.range n, unintegratedCount (Equiv.refl (Fin n)) (k + 1) =
      n - 1 - k := by
    intro k hk
    have hkn := Finset.mem_range.mp hk
    rw [unintegratedCount_refl, Nat.min_eq_left (by omega)]
    omega
  rw [Finset.sum_congr rfl h, Finset.sum_range_reflect (λ j => j) n]
  have h2 := Finset.sum_range_id_mul_two n
  omega

/-- The nested (German) cluster costs `n(n−1)`: all `n` NPs float until the last
verb. -/
theorem totalIntegrationCost_revPerm (n : ℕ) :
    totalIntegrationCost (Fin.revPerm : Equiv.Perm (Fin n)) = n * (n - 1) := by
  unfold totalIntegrationCost
  cases n with
  | zero => simp
  | succ m =>
    have h : ∀ k ∈ Finset.range m,
        unintegratedCount (Fin.revPerm : Equiv.Perm (Fin (m + 1))) (k + 1) = m + 1 := by
      intro k hk
      have hkm := Finset.mem_range.mp hk
      rw [unintegratedCount_revPerm, ite_eq_right (by omega)]
    rw [Finset.sum_range_succ, Finset.sum_const_nat h, Finset.card_range,
        unintegratedCount_revPerm, ite_eq_left (by omega)]
    have := Nat.mul_comm m (m + 1)
    simp only [Nat.add_sub_cancel]
    omega

theorem totalIntegrationCost_revPerm_eq_two_mul (n : ℕ) :
    totalIntegrationCost (Fin.revPerm : Equiv.Perm (Fin n)) =
      2 * totalIntegrationCost (Equiv.refl (Fin n)) := by
  rw [totalIntegrationCost_refl, totalIntegrationCost_revPerm]
  have h2 := Finset.sum_range_id_mul_two n
  omega

theorem crossed_lt_nested (hn : 2 ≤ n) :
    totalIntegrationCost (Equiv.refl (Fin n)) <
      totalIntegrationCost (Fin.revPerm : Equiv.Perm (Fin n)) := by
  rw [totalIntegrationCost_refl, totalIntegrationCost_revPerm]
  have h : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  omega

/-- The gap equals the whole crossed cost `n(n−1)/2`. -/
theorem cost_gap (n : ℕ) :
    totalIntegrationCost (Fin.revPerm : Equiv.Perm (Fin n)) -
        totalIntegrationCost (Equiv.refl (Fin n)) =
      totalIntegrationCost (Equiv.refl (Fin n)) := by
  rw [totalIntegrationCost_revPerm_eq_two_mul]; omega

theorem level_costs :
    (totalIntegrationCost (Equiv.refl (Fin 2)),
      totalIntegrationCost (Equiv.refl (Fin 3)),
      totalIntegrationCost (Equiv.refl (Fin 4))) = (1, 3, 6) ∧
    (totalIntegrationCost (Fin.revPerm : Equiv.Perm (Fin 2)),
      totalIntegrationCost (Fin.revPerm : Equiv.Perm (Fin 3)),
      totalIntegrationCost (Fin.revPerm : Equiv.Perm (Fin 4))) = (2, 6, 12) := by
  simp [totalIntegrationCost_refl, totalIntegrationCost_revPerm]

/-- The nested binding is antitone — the projective, stack-parsable pattern
([bresnan-etal-1982]) — and the crossed one is not; the costs run the other way,
so parsing difficulty does not track stack-parsability. -/
theorem nonprojective_is_cheaper (hn : 2 ≤ n) :
    ¬Antitone ⇑(Equiv.refl (Fin n)) ∧ Antitone ⇑(Fin.revPerm : Equiv.Perm (Fin n)) ∧
      totalIntegrationCost (Equiv.refl (Fin n)) <
        totalIntegrationCost (Fin.revPerm : Equiv.Perm (Fin n)) := by
  refine ⟨fun h => ?_, fun i j hij => ?_, crossed_lt_nested hn⟩
  · have := h (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) (by simp [Fin.mk_le_mk])
    simp [Fin.le_def] at this
  · simpa using Fin.rev_le_rev.2 hij

end BachBrownMarslenWilson1986
