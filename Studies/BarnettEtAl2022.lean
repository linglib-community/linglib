module

public import Linglib.Core.Combinatorics.SetFamily.FourFunctions
public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Core.Probability.Kernel.Posterior
public import Linglib.Core.Probability.UniformOn
public import Linglib.Pragmatics.RSA.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.GetD
public import Mathlib.Order.UpperLower.Basic

/-!
# Barnett, Griffiths and Hawkins (2022): A Pragmatic Account of the Weak Evidence Effect

In the Stick Contest a judge decides whether five hidden sticks, each one to nine inches long,
are longer than five inches on average, after a contestant who wants the verdict *longer*
reveals one of them. A literal listener takes the stick at face value. A persuasive speaker
reveals a stick with weight `L0(longer | u)^β`, so a pragmatic listener who expects such a
speaker takes a weak stick as a sign that no stronger one was available.

The pragmatic listener discounts every stick and still believes more in *longer* the longer the
stick shown. The sticks that backfire, evidence for *longer* that lowers the belief in it below
the prior, therefore form an interval, and there are none without a persuasive goal. As the
bias grows the speaker shows the longest stick, the listener's belief tends to the probability
of *longer* given that the longest stick has the length shown, and the sticks of length five to
seven backfire while the longer ones do not.

## Implementation notes

* As in the authors' code, the sticks are independent and uniform, an average of exactly five
  counts as *longer*, the speaker chooses which of the five sticks to reveal, and the literal
  listener conditions on one given stick having the length shown. The verdict is computed
  exactly, where the code's floating-point mean misclassifies some ties.
* The paper's Figure 3A used sticks of length `0` to `10` and measures the effect against `0.5`.
  Here sticks run from `1` to `9`, as in the experiment and the fitted model, and the effect is
  measured against the prior; with these sticks a shown `8` does not backfire.
* Counts are tabulated by total one stick at a time, so the kernel never enumerates tuples.

## TODO

* The finite-bias values of the simulation are numerical: near the fitted bias `β ≈ 2` sticks of
  length five and six backfire, and the backfiring range widens with `β`. The belief itself is
  not antitone in `β` (a shown `9` is not), so the widening is a property of the set.

## References

* [barnett-griffiths-hawkins-2022]
* [holley-1974]
-/

@[expose] public section

open Finset Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal

namespace BarnettEtAl2022

/-! ### The Stick Contest -/

/-- The length of a stick, from `1` to `9` inches. -/
def length (i : Fin 9) : ℕ := i + 1

theorem length_mono : Monotone length := fun _ _ h ↦ Nat.succ_le_succ h

variable (n : ℕ)

/-- The verdict *longer* holds of `n + 1` sticks whose average is at least the midpoint of five
inches. -/
def longer : Set (Fin (n + 1) → Fin 9) := {w | 5 * (n + 1) ≤ ∑ i, length (w i)}

instance (w : Fin (n + 1) → Fin 9) : Decidable (w ∈ longer n) := Nat.decLe _ _

theorem isUpperSet_longer : IsUpperSet (longer n) :=
  fun _ _ hvw hv ↦ hv.trans (sum_le_sum fun i _ ↦ length_mono (hvw i))

variable {n}

theorem cons_mem_longer {u : Fin 9} {x : Fin n → Fin 9} :
    Fin.cons u x ∈ longer n ↔ 5 * (n + 1) ≤ length u + ∑ i, length (x i) := by
  simp [longer, Fin.sum_univ_succ]

theorem insertNth_mem_longer (i : Fin (n + 1)) (u : Fin 9) (x : Fin n → Fin 9) :
    Fin.insertNth i u x ∈ longer n ↔ Fin.cons u x ∈ longer n := by
  simp only [longer, Set.mem_ofPred_eq]
  rw [Fin.sum_univ_succAbove _ i, Fin.sum_univ_succ]
  simp

theorem exists_sum_length_eq {t : ℕ} (h₁ : n ≤ t) (h₂ : t ≤ 9 * n) :
    ∃ x : Fin n → Fin 9, ∑ i, length (x i) = t := by
  induction n generalizing t with
  | zero => exact ⟨finZeroElim, by simp; omega⟩
  | succ n ih =>
    obtain ⟨x, hx⟩ := ih (t := t - min 9 (t - n)) (by omega) (by omega)
    refine ⟨Fin.cons ⟨min 9 (t - n) - 1, by omega⟩ x, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hx, length]
    simp only
    omega

theorem sum_cons {M : Type*} [AddCommMonoid M] (f : (Fin (n + 1) → Fin 9) → M) :
    ∑ w, f w = ∑ u, ∑ x : Fin n → Fin 9, f (Fin.cons u x) := by
  rw [← (Fin.consEquiv fun _ ↦ Fin 9).sum_comp, Fintype.sum_prod_type]
  rfl

/-! ### The literal listener -/

variable (n) in
/-- The literal listener's belief in *longer* is that of the uniform prior conditioned on the
revealed stick, taken to be the first, having length `u`. -/
noncomputable def literal (u : Fin 9) : ℝ :=
  (uniformOn {w : Fin (n + 1) → Fin 9 | w 0 = u}).real (longer n)

theorem literal_eq_card (u : Fin 9) :
    literal n u = #{x : Fin n → Fin 9 | Fin.cons u x ∈ longer n} / 9 ^ n := by
  rw [literal, uniformOn_real_apply]
  have h : {w : Fin (n + 1) → Fin 9 | w 0 = u} = Fin.cons u '' Set.univ := by
    ext w
    refine ⟨fun hw ↦ ⟨Fin.tail w, trivial, by rw [← hw]; exact Fin.cons_self_tail w⟩, ?_⟩
    rintro ⟨x, -, rfl⟩
    simp
  rw [h, ← Set.image_inter_preimage,
    Set.ncard_image_of_injective _ (Fin.cons_right_injective (α := fun _ ↦ Fin 9) u),
    Set.ncard_image_of_injective _ (Fin.cons_right_injective (α := fun _ ↦ Fin 9) u),
    Set.ncard_univ, Nat.card_eq_fintype_card, Set.univ_inter, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]
  simp only [show Fin.cons u ⁻¹' longer n =
      ↑(univ.filter fun x : Fin n → Fin 9 ↦ Fin.cons u x ∈ longer n) by ext; simp,
    Set.ncard_coe_finset]
  push_cast
  rfl

theorem prior_eq_average :
    (uniformOn Set.univ).real (longer n) = (∑ u, literal n u) / 9 := by
  have h : #{w : Fin (n + 1) → Fin 9 | w ∈ longer n} =
      ∑ u, #{x : Fin n → Fin 9 | Fin.cons u x ∈ longer n} := by
    simp only [card_filter]
    exact sum_cons _
  rw [uniformOn_univ_real_apply, show longer n = ↑(univ.filter (· ∈ longer n)) by ext; simp,
    Set.ncard_coe_finset, h, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  simp only [literal_eq_card]
  push_cast
  rw [← sum_div, div_div, pow_succ]

private theorem sum_card_filter_mul {u : Fin 9} {G : (Fin (n + 1) → Fin 9) → ℝ}
    (hG : ∀ i x, G (Fin.insertNth i u x) = G (Fin.cons u x)) :
    ∑ w, (#{i | w i = u} : ℝ) * G w = (n + 1) * ∑ x : Fin n → Fin 9, G (Fin.cons u x) := by
  have h (i : Fin (n + 1)) :
      ∑ w, (if w i = u then G w else 0) = ∑ x : Fin n → Fin 9, G (Fin.cons u x) := by
    rw [← (Fin.insertNthEquiv (fun _ ↦ Fin 9) i).sum_comp, Fintype.sum_prod_type, sum_comm]
    simp only [Fin.insertNthEquiv_apply, Fin.insertNth_apply_same, sum_ite_eq', mem_univ,
      ite_true]
    exact sum_congr rfl fun x _ ↦ hG i x
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, sum_mul,
    ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_succ]

private theorem sum_rpow_insertNth (β : ℝ) (i : Fin (n + 1)) (u : Fin 9) (x : Fin n → Fin 9) :
    ∑ j, literal n ((Fin.insertNth i u x : Fin (n + 1) → Fin 9) j) ^ β =
      literal n u ^ β + ∑ j, literal n (x j) ^ β := by
  rw [Fin.sum_univ_succAbove _ i]
  simp

private theorem sum_rpow_cons (β : ℝ) (u : Fin 9) (x : Fin n → Fin 9) :
    ∑ j, literal n ((Fin.cons u x : Fin (n + 1) → Fin 9) j) ^ β =
      literal n u ^ β + ∑ j, literal n (x j) ^ β := by
  rw [Fin.sum_univ_succ]
  simp

private theorem sum_rpow_inf_add_sup (β : ℝ) (x y : Fin n → Fin 9) :
    ∑ i, literal n ((x ⊓ y) i) ^ β + ∑ i, literal n ((x ⊔ y) i) ^ β =
      ∑ i, literal n (x i) ^ β + ∑ i, literal n (y i) ^ β := by
  simp only [← sum_add_distrib, Pi.inf_apply, Pi.sup_apply]
  refine sum_congr rfl fun i _ ↦ ?_
  rcases le_total (x i) (y i) with h | h
  · rw [inf_eq_left.2 h, sup_eq_right.2 h]
  · rw [inf_eq_right.2 h, sup_eq_left.2 h, add_comm]

private theorem isUpperSet_cons_mem_longer (u : Fin 9) :
    IsUpperSet (↑(univ.filter fun x : Fin n → Fin 9 ↦ Fin.cons u x ∈ longer n) :
      Set (Fin n → Fin 9)) := by
  simp only [coe_filter, mem_univ, true_and]
  exact (isUpperSet_longer n).preimage fun _ _ hxy ↦ Fin.cons_le_cons.2 ⟨le_rfl, hxy⟩

private theorem card_sup_pos (w : Fin (n + 1) → Fin 9) : 0 < #{j | w j = univ.sup w} := by
  obtain ⟨j, -, hj⟩ := exists_mem_eq_sup univ univ_nonempty w
  exact card_pos.2 ⟨j, mem_filter.2 ⟨mem_univ _, hj.symm⟩⟩

section NeZero

variable [NeZero n]

theorem literal_pos (u : Fin 9) : 0 < literal n u := by
  rw [literal_eq_card]
  refine div_pos (Nat.cast_pos.2 (card_pos.2 ⟨⊤, mem_filter.2 ⟨mem_univ _, ?_⟩⟩)) (by positivity)
  have := NeZero.ne n
  simp only [cons_mem_longer, Pi.top_apply, Fin.top_eq_last, length, Fin.val_last, sum_const,
    card_univ, Fintype.card_fin, smul_eq_mul]
  omega

theorem literal_strictMono : StrictMono (literal n) := fun u v huv ↦ by
  have hn := NeZero.ne n
  have hv : 1 ≤ (v : ℕ) := lt_of_le_of_lt (Nat.zero_le _) huv
  obtain ⟨x, hx⟩ := exists_sum_length_eq (n := n) (t := 5 * (n + 1) - length v)
    (by simp only [length]; omega) (by simp only [length]; omega)
  simp only [literal_eq_card]
  refine div_lt_div_of_pos_right ?_ (by positivity)
  refine Nat.cast_lt.2 (card_lt_card ((ssubset_iff_of_subset ?_).2 ⟨x, ?_, ?_⟩))
  · refine monotone_filter_right _ fun y _ hy ↦ ?_
    rw [cons_mem_longer] at hy ⊢
    exact hy.trans (Nat.add_le_add_right (length_mono huv.le) _)
  · simp only [mem_filter, mem_univ, true_and, cons_mem_longer, hx]
    omega
  · simp only [mem_filter, mem_univ, true_and, cons_mem_longer, length] at *
    omega

theorem literal_mono : Monotone (literal n) := literal_strictMono.monotone

/-! ### The persuasive speaker and the pragmatic listener -/

variable (n) in
/-- The persuasive speaker chooses which stick to reveal, with weight `L0(longer | u)^β`. -/
noncomputable def reveal (β : ℝ) : Kernel (Fin (n + 1) → Fin 9) (Fin (n + 1)) :=
  Kernel.ofWeights fun w i ↦ ENNReal.ofReal (literal n (w i) ^ β)

theorem reveal_eq_softmax (β : ℝ) :
    reveal n β = Kernel.softmax fun w i ↦ ((β * Real.log (literal n (w i)) : ℝ) : EReal) := by
  unfold reveal Kernel.softmax
  congr 1
  funext w i
  rw [EReal.exp_coe, Real.rpow_def_of_pos (literal_pos _), mul_comm]

instance (β : ℝ) : IsMarkovKernel (reveal n β) :=
  Kernel.isMarkovKernel_ofWeights
    (fun _ ↦ ⟨0, (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (literal_pos _) β)).ne'⟩)
    fun _ _ ↦ ENNReal.ofReal_ne_top

variable (n) in
/-- The speaker as the listener hears it reports the length of the revealed stick. -/
noncomputable def speaker (β : ℝ) : Kernel (Fin (n + 1) → Fin 9) (Fin 9) :=
  Kernel.ofFunOfCountable fun w ↦ (reveal n β w).map w

instance (β : ℝ) : IsMarkovKernel (speaker n β) :=
  ⟨fun w ↦ by
    rw [speaker, Kernel.ofFunOfCountable_apply]
    infer_instance⟩

variable (n) in
/-- The pragmatic listener inverts the speaker against the uniform prior. -/
noncomputable def pragmaticListener (β : ℝ) : Kernel (Fin 9) (Fin (n + 1) → Fin 9) :=
  RSA.listener (uniformOn Set.univ) (speaker n β)

variable (n) in
/-- The speaker's probability of revealing the stick `u` rather than one of the others `x`. -/
noncomputable def share (β : ℝ) (u : Fin 9) (x : Fin n → Fin 9) : ℝ :=
  literal n u ^ β / (literal n u ^ β + ∑ i, literal n (x i) ^ β)

theorem reveal_real_singleton (β : ℝ) (w : Fin (n + 1) → Fin 9) (i : Fin (n + 1)) :
    (reveal n β w).real {i} = literal n (w i) ^ β / ∑ j, literal n (w j) ^ β := by
  rw [reveal, Kernel.ofWeights_real_singleton _ _ fun _ ↦ ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (literal_pos _) β).le]

private theorem rpow_literal_pos (β : ℝ) (u : Fin 9) : 0 < literal n u ^ β :=
  Real.rpow_pos_of_pos (literal_pos u) β

theorem speaker_real_singleton (β : ℝ) (w : Fin (n + 1) → Fin 9) (u : Fin 9) :
    (speaker n β w).real {u} = ∑ i with w i = u, (reveal n β w).real {i} := by
  rw [speaker, Kernel.ofFunOfCountable_apply, map_measureReal_apply_of_aemeasurable
    (measurable_of_countable w).aemeasurable (measurableSet_singleton u),
    show w ⁻¹' {u} = ↑(univ.filter fun i ↦ w i = u) by ext; simp, sum_measureReal_singleton]

theorem speaker_real_singleton_eq_mul (β : ℝ) (w : Fin (n + 1) → Fin 9) (u : Fin 9) :
    (speaker n β w).real {u} = #{i | w i = u} * (literal n u ^ β / ∑ j, literal n (w j) ^ β) := by
  rw [speaker_real_singleton, ← nsmul_eq_mul, ← sum_const]
  exact sum_congr rfl fun i hi ↦ by rw [reveal_real_singleton, (mem_filter.1 hi).2]

theorem share_pos (β : ℝ) (u : Fin 9) (x : Fin n → Fin 9) : 0 < share n β u x :=
  div_pos (rpow_literal_pos β u)
    (add_pos_of_pos_of_nonneg (rpow_literal_pos β u)
      (sum_nonneg fun _ _ ↦ (rpow_literal_pos β _).le))

theorem pragmaticListener_real_longer (β : ℝ) (u : Fin 9) :
    (pragmaticListener n β u).real (longer n) =
      (∑ x with Fin.cons u x ∈ longer n, share n β u x) / ∑ x, share n β u x := by
  let G : (Fin (n + 1) → Fin 9) → ℝ := fun w ↦ literal n u ^ β / ∑ j, literal n (w j) ^ β
  have hG (i : Fin (n + 1)) (x : Fin n → Fin 9) : G (Fin.insertNth i u x) = G (Fin.cons u x) := by
    simp only [G, sum_rpow_insertNth, sum_rpow_cons]
  have hGl (i : Fin (n + 1)) (x : Fin n → Fin 9) :
      (if Fin.insertNth i u x ∈ longer n then G (Fin.insertNth i u x) else 0) =
        if Fin.cons u x ∈ longer n then G (Fin.cons u x) else 0 := by
    simp only [insertNth_mem_longer, hG]
  have key := RSA.listener_uniformOn_univ_real_finset (speaker n β) u
    (univ.filter (· ∈ longer n))
  simp only [coe_filter, mem_univ, true_and, Set.ofPred_mem_eq] at key
  have hs (w : Fin (n + 1) → Fin 9) : (speaker n β w).real {u} = #{i | w i = u} * G w := by
    rw [speaker_real_singleton_eq_mul]
  rw [pragmaticListener, key, sum_congr rfl fun w _ ↦ hs w, sum_congr rfl fun w _ ↦ hs w,
    sum_filter]
  simp_rw [← mul_ite_zero]
  rw [sum_card_filter_mul hGl, sum_card_filter_mul hG, mul_div_mul_left _ _ (by positivity),
    sum_filter]
  simp only [G, sum_rpow_cons]
  rfl

/-! ### Discounting -/

private theorem rpow_literal_mono {β : ℝ} (hβ : 0 ≤ β) : Monotone fun u ↦ literal n u ^ β :=
  fun _ _ h ↦ Real.rpow_le_rpow (literal_pos _).le (literal_mono h) hβ

private theorem sum_rpow_mono {β : ℝ} (hβ : 0 ≤ β) :
    Monotone fun x : Fin n → Fin 9 ↦ ∑ i, literal n (x i) ^ β :=
  fun _ _ hxy ↦ sum_le_sum fun i _ ↦ rpow_literal_mono hβ (hxy i)

private theorem add_sum_rpow_pos (β : ℝ) (u : Fin 9) (x : Fin n → Fin 9) :
    0 < literal n u ^ β + ∑ i, literal n (x i) ^ β :=
  add_pos_of_pos_of_nonneg (rpow_literal_pos β u) (sum_nonneg fun _ _ ↦ (rpow_literal_pos β _).le)

theorem share_antitone {β : ℝ} (hβ : 0 ≤ β) (u : Fin 9) : Antitone (share n β u) :=
  fun x _ hxy ↦ div_le_div_of_nonneg_left (rpow_literal_pos β u).le (add_sum_rpow_pos β u x)
    (add_le_add le_rfl (sum_rpow_mono hβ hxy))

private theorem mul_le_mul_of_add_eq {p q a b m M : ℝ} (hpq : p ≤ q) (ha : m ≤ a) (hb : m ≤ b)
    (h : m + M = a + b) : (p + m) * (q + M) ≤ (p + a) * (q + b) := by
  obtain rfl : M = a + b - m := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hpq),
    mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem share_mul_share_le {β : ℝ} (hβ : 0 ≤ β) {u v : Fin 9} (huv : u ≤ v)
    (x y : Fin n → Fin 9) :
    share n β u x * share n β v y ≤ share n β u (x ⊓ y) * share n β v (x ⊔ y) := by
  simp only [share, div_mul_div_comm]
  exact div_le_div_of_nonneg_left (mul_pos (rpow_literal_pos β u) (rpow_literal_pos β v)).le
    (mul_pos (add_sum_rpow_pos β u _) (add_sum_rpow_pos β v _))
    (mul_le_mul_of_add_eq (rpow_literal_mono hβ huv) (sum_rpow_mono hβ inf_le_left)
      (sum_rpow_mono hβ inf_le_right) (sum_rpow_inf_add_sup β x y))

private theorem sum_share_pos (β : ℝ) (u : Fin 9) : 0 < ∑ x : Fin n → Fin 9, share n β u x :=
  sum_pos (fun x _ ↦ share_pos β u x) univ_nonempty

/-- The pragmatic listener discounts every stick. -/
theorem pragmaticListener_real_le_literal {β : ℝ} (hβ : 0 ≤ β) (u : Fin 9) :
    (pragmaticListener n β u).real (longer n) ≤ literal n u := by
  have h := holley_isUpperSet (g := (1 : (Fin n → Fin 9) → ℝ)) (fun x ↦ (share_pos β u x).le)
    (fun _ ↦ zero_le_one) (isUpperSet_cons_mem_longer u)
    fun a b ↦ by simpa using share_antitone hβ u (inf_le_left : a ⊓ b ≤ a)
  simp only [Pi.one_apply, sum_const, card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun,
    Fintype.card_fin] at h
  rw [pragmaticListener_real_longer, literal_eq_card, div_le_div_iff₀ (sum_share_pos β u)
    (by positivity)]
  push_cast at h ⊢
  linarith

theorem pragmaticListener_zero (u : Fin 9) :
    (pragmaticListener n 0 u).real (longer n) = literal n u := by
  have h (x : Fin n → Fin 9) : share n 0 u x = 1 / (n + 1) := by
    simp only [share, Real.rpow_zero, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    ring
  simp only [pragmaticListener_real_longer, h, sum_const, nsmul_eq_mul, literal_eq_card,
    card_univ, Fintype.card_fun, Fintype.card_fin]
  push_cast
  field_simp

/-- The pragmatic belief in *longer* grows with the stick shown. -/
theorem pragmaticListener_real_mono {β : ℝ} (hβ : 0 ≤ β) :
    Monotone fun u ↦ (pragmaticListener n β u).real (longer n) := fun u v huv ↦ by
  have h := holley_isUpperSet (fun x ↦ (share_pos (n := n) β u x).le)
    (fun x ↦ (share_pos β v x).le) (isUpperSet_cons_mem_longer v) (share_mul_share_le hβ huv)
  have hsub : ∑ x with Fin.cons u x ∈ longer n, share n β u x ≤
      ∑ x with Fin.cons v x ∈ longer n, share n β u x := by
    refine sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ fun x _ hx ↦ ?_)
      fun x _ _ ↦ (share_pos β u x).le
    rw [cons_mem_longer] at hx ⊢
    exact hx.trans (Nat.add_le_add_right (length_mono huv) _)
  simp only [sum_filter] at h
  simp only [pragmaticListener_real_longer, sum_filter] at hsub ⊢
  rw [div_le_div_iff₀ (sum_share_pos (n := n) β u) (sum_share_pos β v)]
  nlinarith [mul_le_mul_of_nonneg_right hsub (sum_share_pos (n := n) β v).le]

variable (n) in
/-- A stick backfires at bias `β` when it is literal evidence for *longer* but, revealed by the
persuasive speaker, lowers the belief in *longer* below the prior. -/
def backfires (β : ℝ) : Set (Fin 9) :=
  {u | (uniformOn Set.univ).real (longer n) < literal n u ∧
    (pragmaticListener n β u).real (longer n) < (uniformOn Set.univ).real (longer n)}

/-- The backfiring sticks form an interval, empty without a persuasive goal. -/
theorem backfires_zero : backfires n 0 = ∅ :=
  Set.eq_empty_of_forall_notMem fun u ⟨h₁, h₂⟩ ↦ by
    rw [pragmaticListener_zero] at h₂
    exact h₂.not_gt h₁

/-- The sticks that backfire form an interval. -/
theorem ordConnected_backfires {β : ℝ} (hβ : 0 ≤ β) : (backfires n β).OrdConnected :=
  IsUpperSet.ordConnected (s := {u | (uniformOn Set.univ).real (longer n) < literal n u})
      (fun _ _ h hu ↦ hu.trans_le (literal_mono h)) |>.inter <|
    IsLowerSet.ordConnected
      (s := {u | (pragmaticListener n β u).real (longer n) < (uniformOn Set.univ).real (longer n)})
      fun _ _ h hu ↦ (pragmaticListener_real_mono hβ h).trans_lt hu

/-! ### A fully persuasive speaker -/

private theorem tendsto_div_rpow (w : Fin (n + 1) → Fin 9) (j : Fin (n + 1)) :
    Tendsto (fun β : ℝ ↦ (literal n (w j) / literal n (univ.sup w)) ^ β) atTop
      (𝓝 (if w j = univ.sup w then 1 else 0)) := by
  split_ifs with h
  · simp only [h, div_self (literal_pos _).ne', Real.one_rpow]
    exact tendsto_const_nhds
  · exact tendsto_rpow_atTop_of_base_lt_one _
      (neg_one_lt_zero.trans (div_pos (literal_pos _) (literal_pos _)))
      ((div_lt_one (literal_pos _)).2
        (literal_strictMono (lt_of_le_of_ne (le_sup (mem_univ j)) h)))

theorem tendsto_reveal_real_singleton_atTop (w : Fin (n + 1) → Fin 9) (i : Fin (n + 1)) :
    Tendsto (fun β ↦ (reveal n β w).real {i}) atTop
      (𝓝 ((if w i = univ.sup w then 1 else 0) / #{j | w j = univ.sup w})) := by
  have hs := literal_pos (n := n) (univ.sup w)
  have hform (β : ℝ) : (reveal n β w).real {i} =
      (literal n (w i) / literal n (univ.sup w)) ^ β /
        ∑ j, (literal n (w j) / literal n (univ.sup w)) ^ β := by
    rw [reveal_real_singleton]
    simp only [Real.div_rpow (literal_pos _).le hs.le]
    rw [← sum_div, div_div_div_cancel_right₀ (Real.rpow_pos_of_pos hs β).ne']
  simp_rw [hform]
  rw [← sum_boole]
  refine (tendsto_div_rpow w i).div (tendsto_finsetSum _ fun j _ ↦ tendsto_div_rpow w j) ?_
  rw [sum_boole]
  exact_mod_cast (card_sup_pos w).ne'

/-- As the bias grows the speaker shows the longest stick with certainty. -/
theorem tendsto_speaker_real_singleton_atTop (w : Fin (n + 1) → Fin 9) (u : Fin 9) :
    Tendsto (fun β ↦ (speaker n β w).real {u}) atTop (𝓝 (if u = univ.sup w then 1 else 0)) := by
  simp_rw [speaker_real_singleton]
  convert tendsto_finsetSum {i | w i = u} fun i _ ↦ tendsto_reveal_real_singleton_atTop w i
    using 2
  split_ifs with hu
  · subst hu
    rw [sum_congr rfl fun i hi ↦ by rw [ite_eq_left_iff.2 fun h ↦ absurd (mem_filter.1 hi).2 h],
      sum_const, nsmul_eq_mul, mul_one_div, div_self]
    exact_mod_cast (card_sup_pos w).ne'
  · refine (sum_eq_zero fun i hi ↦ ?_).symm
    rw [ite_eq_right_iff.2 fun h ↦ absurd ((mem_filter.1 hi).2.symm.trans h) hu, zero_div]

/-- As the bias grows the pragmatic listener's beliefs tend to the uniform prior conditioned on
the shown stick being the longest. -/
theorem tendsto_pragmaticListener_real_atTop (u : Fin 9) (E : Set (Fin (n + 1) → Fin 9)) :
    Tendsto (fun β ↦ (pragmaticListener n β u).real E) atTop
      (𝓝 ((uniformOn {w : Fin (n + 1) → Fin 9 | univ.sup w = u}).real E)) := by
  classical
  have hform (β : ℝ) : (pragmaticListener n β u).real E =
      (∑ w with w ∈ E, (speaker n β w).real {u}) / ∑ w, (speaker n β w).real {u} := by
    have key := RSA.listener_uniformOn_univ_real_finset (speaker n β) u (univ.filter (· ∈ E))
    simp only [coe_filter, mem_univ, true_and, Set.ofPred_mem_eq] at key
    rw [pragmaticListener, key]
  have h (w : Fin (n + 1) → Fin 9) := tendsto_speaker_real_singleton_atTop w u
  have hS : {w : Fin (n + 1) → Fin 9 | univ.sup w = u} =
      ↑(univ.filter fun w : Fin (n + 1) → Fin 9 ↦ u = univ.sup w) := by
    ext; simp [eq_comm]
  have hSE : {w : Fin (n + 1) → Fin 9 | univ.sup w = u} ∩ E =
      ↑(univ.filter fun w : Fin (n + 1) → Fin 9 ↦ w ∈ E ∧ u = univ.sup w) := by
    ext; simp [eq_comm, and_comm]
  rw [uniformOn_real_apply, hSE, hS, Set.ncard_coe_finset, Set.ncard_coe_finset, ← filter_filter,
    ← sum_boole, ← sum_boole]
  simp_rw [hform]
  refine (tendsto_finsetSum _ fun w _ ↦ h w).div (tendsto_finsetSum _ fun w _ ↦ h w) ?_
  rw [sum_boole]
  exact (Nat.cast_pos.2 (card_pos.2 ⟨fun _ ↦ u, mem_filter.2 ⟨mem_univ _,
    (sup_const univ_nonempty u).symm⟩⟩)).ne'

end NeZero

theorem listener_dirac_sup (u : Fin 9) :
    RSA.listener (uniformOn Set.univ)
        (fun w : Fin (n + 1) → Fin 9 ↦ Measure.dirac (univ.sup w)) u =
      uniformOn {w : Fin (n + 1) → Fin 9 | univ.sup w = u} := by
  rw [RSA.listener_dirac_apply _ (measurable_of_countable _)]
  unfold uniformOn
  rw [cond_cond_eq_cond_inter MeasurableSet.univ (Set.toFinite _).measurableSet, Set.univ_inter]
  rfl

/-! ### Counting sticks by their total -/

/-- For each `k`, the number of `n` sticks of index below `m` totalling at least `k` inches,
tabulated one stick at a time. -/
private def tails (m : ℕ) : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => (List.range (m * (n + 1) + 1)).map fun k ↦
      ∑ a ∈ range m, (tails m n).getD (k - (a + 1)) 0

private theorem length_tails (m n : ℕ) : (tails m n).length = m * n + 1 := by
  cases n <;> simp [tails]

private theorem card_tails {m : ℕ} (hm : m ≤ 9) (k : ℕ) :
    #{x : Fin n → Fin 9 | (∀ i, (x i : ℕ) < m) ∧ k ≤ ∑ i, length (x i)} =
      (tails m n).getD k 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp [tails]
  | succ n ih =>
    have hcons (a : Fin 9) : ∑ y : Fin n → Fin 9,
        (if (∀ i, ((Fin.cons a y : Fin (n + 1) → Fin 9) i : ℕ) < m) ∧
          k ≤ ∑ i, length ((Fin.cons a y : Fin (n + 1) → Fin 9) i) then 1 else 0) =
          if (a : ℕ) < m then (tails m n).getD (k - (a + 1)) 0 else 0 := by
      simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ]
      split_ifs with ha
      · rw [← ih, card_filter]
        refine sum_congr rfl fun y _ ↦ ?_
        simp only [ha, true_and, length, Nat.sub_le_iff_le_add, add_comm]
      · simp [ha]
    rw [card_filter, sum_cons]
    simp only [hcons]
    rw [Fin.sum_univ_eq_sum_range (fun a ↦ if a < m then (tails m n).getD (k - (a + 1)) 0 else 0),
      ← sum_filter, show (range 9).filter (· < m) = range m by ext; simp; omega, tails]
    by_cases hk : k < m * (n + 1) + 1
    · simp [List.getD_eq_getElem?_getD, hk]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hk), Option.getD_none]
      refine sum_eq_zero fun a ha ↦ List.getD_eq_default (l := tails m n) (d := 0) ?_
      rw [length_tails]
      simp only [mem_range] at ha
      rw [Nat.mul_succ] at hk
      generalize m * n = p at *
      omega

private theorem card_sup_eq (u : Fin 9) (E : (Fin (n + 1) → Fin 9) → Prop) [DecidablePred E] :
    #{w | univ.sup w = u ∧ E w} =
      #{w | (∀ i, (w i : ℕ) < u + 1) ∧ E w} - #{w | (∀ i, (w i : ℕ) < u) ∧ E w} := by
  have h := card_filter_add_card_filter_not
    (s := univ.filter fun w : Fin (n + 1) → Fin 9 ↦ (∀ i, (w i : ℕ) < u + 1) ∧ E w)
    fun w ↦ ∀ i, (w i : ℕ) < u
  rw [filter_filter, filter_filter] at h
  have h₁ : #{w : Fin (n + 1) → Fin 9 | ((∀ i, (w i : ℕ) < u + 1) ∧ E w) ∧ ∀ i, (w i : ℕ) < u} =
      #{w | (∀ i, (w i : ℕ) < u) ∧ E w} :=
    congrArg card (filter_congr fun w _ ↦
      ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨fun i ↦ (h.1 i).trans (Nat.lt_succ_self _), h.2⟩, h.1⟩⟩)
  have h₂ : #{w : Fin (n + 1) → Fin 9 | ((∀ i, (w i : ℕ) < u + 1) ∧ E w) ∧ ¬∀ i, (w i : ℕ) < u} =
      #{w | univ.sup w = u ∧ E w} := by
    refine congrArg card (filter_congr fun w _ ↦ ?_)
    obtain ⟨j, -, hj⟩ := exists_mem_eq_sup univ univ_nonempty w
    simp only [Nat.lt_succ_iff, ← Fin.le_def, ← Fin.lt_def, not_forall, not_lt]
    constructor
    · rintro ⟨⟨h₁, hE⟩, i, hi⟩
      exact ⟨(Finset.sup_le fun i _ ↦ h₁ i).antisymm (hi.trans (le_sup (mem_univ i))), hE⟩
    · rintro ⟨rfl, hE⟩
      exact ⟨⟨fun i ↦ le_sup (mem_univ i), hE⟩, j, hj.le⟩
  omega

/-! ### Five sticks -/

private theorem tails_nine_four : ∀ u : Fin 9, (tails 9 4).getD (25 - length u) 0 =
      ![1680, 2100, 2556, 3036, 3525, 4005, 4461, 4881, 5256] u := by
  decide +kernel

theorem card_cons_mem_longer (u : Fin 9) : #{x : Fin 4 → Fin 9 | Fin.cons u x ∈ longer 4} =
    ![1680, 2100, 2556, 3036, 3525, 4005, 4461, 4881, 5256] u := by
  rw [← tails_nine_four, ← card_tails le_rfl]
  exact congrArg card (filter_congr fun x _ ↦ by
    simp [cons_mem_longer, add_comm, Fin.is_lt])

theorem literal_eq (u : Fin 9) :
    literal 4 u = ![1680, 2100, 2556, 3036, 3525, 4005, 4461, 4881, 5256] u / 6561 := by
  rw [literal_eq_card, card_cons_mem_longer]
  fin_cases u <;> norm_num

theorem prior_eq : (uniformOn Set.univ).real (longer 4) = 3500 / 6561 := by
  rw [prior_eq_average]
  simp only [literal_eq, Fin.sum_univ_succ]
  norm_num

theorem prior_lt_literal_iff {u : Fin 9} :
    (uniformOn Set.univ).real (longer 4) < literal 4 u ↔ 5 ≤ length u := by
  rw [prior_eq, literal_eq]
  fin_cases u <;> norm_num [length]

private theorem card_lt_mem_longer {m : ℕ} (hm : m ≤ 9) :
    #{w : Fin (4 + 1) → Fin 9 | (∀ i, (w i : ℕ) < m) ∧ w ∈ longer 4} = (tails m 5).getD 25 0 :=
  card_tails hm 25

private theorem card_lt {m : ℕ} (hm : m ≤ 9) :
    #{w : Fin (4 + 1) → Fin 9 | (∀ i, (w i : ℕ) < m) ∧ True} = (tails m 5).getD 0 0 := by
  rw [← card_tails hm 0]
  simp

private theorem tails_five : ∀ u : Fin 9,
    ((tails (u + 1) 5).getD 25 0 - (tails u 5).getD 25 0,
      (tails (u + 1) 5).getD 0 0 - (tails u 5).getD 0 0) =
    (![0, 0, 0, 0, 1, 251, 2471, 8821, 19956] u,
      ![1, 31, 211, 781, 2101, 4651, 9031, 15961, 26281] u) := by
  decide +kernel

theorem limit_eq (u : Fin 9) :
    (uniformOn {w : Fin 5 → Fin 9 | univ.sup w = u}).real (longer 4) =
      ![0, 0, 0, 0, 1 / 2101, 251 / 4651, 2471 / 9031, 8821 / 15961, 19956 / 26281] u := by
  have hu := u.is_lt
  rw [uniformOn_real_apply,
    show {w : Fin 5 → Fin 9 | univ.sup w = u} ∩ longer 4 =
      ↑(univ.filter fun w : Fin 5 → Fin 9 ↦ univ.sup w = u ∧ w ∈ longer 4) by ext; simp,
    show {w : Fin 5 → Fin 9 | univ.sup w = u} =
      ↑(univ.filter fun w : Fin 5 → Fin 9 ↦ univ.sup w = u ∧ True) by ext; simp,
    Set.ncard_coe_finset, Set.ncard_coe_finset, card_sup_eq, card_sup_eq,
    card_lt_mem_longer (by omega), card_lt_mem_longer (by omega), card_lt (by omega),
    card_lt (by omega)]
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj (tails_five u)
  rw [h₁, h₂]
  fin_cases u <;> norm_num

/-- For a strongly enough biased speaker the sticks that backfire are exactly those of length
five to seven. -/
theorem eventually_backfires_eq : ∀ᶠ β in atTop, backfires 4 β = length ⁻¹' Set.Icc 5 7 := by
  have hlo : ∀ᶠ β in atTop, (pragmaticListener 4 β 6).real (longer 4) <
      (uniformOn Set.univ).real (longer 4) :=
    (tendsto_pragmaticListener_real_atTop 6 (longer 4)).eventually
      (gt_mem_nhds (by rw [limit_eq, prior_eq]; norm_num))
  have hhi : ∀ᶠ β in atTop, (uniformOn Set.univ).real (longer 4) <
      (pragmaticListener 4 β 7).real (longer 4) :=
    (tendsto_pragmaticListener_real_atTop 7 (longer 4)).eventually
      (lt_mem_nhds (by rw [limit_eq, prior_eq]; norm_num))
  filter_upwards [hlo, hhi, eventually_ge_atTop 0] with β hlo hhi hβ
  ext u
  simp only [backfires, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, prior_lt_literal_iff]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, ?_⟩⟩
  · by_contra h
    refine (hhi.trans_le (pragmaticListener_real_mono hβ (Fin.le_iff_val_le_val.2 ?_))).not_gt h₂
    simp only [length] at h
    simp
    omega
  · refine (pragmaticListener_real_mono hβ (Fin.le_iff_val_le_val.2 ?_)).trans_lt hlo
    simp only [length] at h₂
    simp
    omega

end BarnettEtAl2022
