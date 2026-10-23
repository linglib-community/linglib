module

public import Linglib.Logic.Modal.Epistemic
public import Linglib.Core.Probability.Kernel.OfWeights
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.FixedPoints

/-!
# Fagin and Halpern (1994): Reasoning about Knowledge and Probability

This file formalizes the Kripke structures for knowledge and probability of
[fagin-halpern-1994] and the probabilistic common knowledge of its Section 5. A `KripkeProb`
adds to the accessibility relations of multi-agent epistemic logic (`Logic/Modal/Epistemic`) a
probability space for each agent at each state: a sample space `S_{i,s}` of states and a
probability measure `μ_{i,s}` carried by it. The probability formula `w_i(φ) ≥ b`, "according
to agent `i`, `φ` holds with probability at least `b`", is the set of states `AtLeast b i φ`.
Knowledge and probability are otherwise independent, so an agent need not know their own
probability space, which is what lets the paper's coin-toss example come out right. The
conditions the paper considers on the pair are `CONS` (the sample space lies within the
states the agent considers possible), `OBJ` (all agents share one space), `SDP` (the space is
determined by the agent's information cell) and `UNIF` (the space is the same at every state
of the sample space); `UNIF.of_cons_sdp` is the paper's remark that the first and third imply
the fourth. The correspondence of Section 4 between these conditions and axioms is proved in
its sound direction: W7, knowledge implies probability one under `CONS`
(`real_eq_one_of_knows`); W9, a probability formula true at a state has probability one there
under `UNIF` (`UNIF.real_atLeast_eq_one`, `UNIF.real_compl_atLeast_eq_one`); W10, a
probability formula true at a state is known there under `SDP` (`SDP.knows_atLeast`,
`SDP.knows_compl_atLeast`); and Miller's principle `w_i(φ) ≥ b · w_i(w_i(φ) ≥ b)`, which
`UNIF` validates (`UNIF.miller`).

Section 5 defines `E_G^b φ` (`EveryoneProb`: every member of `G` knows that their probability
of `φ` is at least `b`) and probabilistic common knowledge `C_G^b φ` (`CommonProb`) as the
intersection of the iterates `(F_G^b)^k φ` of `X ↦ E_G^b (φ ∩ X)` rather than of the iterates
of `E_G^b` alone. `commonProb_eq_gfp` is Lemma 5.1: `C_G^b φ` is the greatest fixed point of
`X ⇔ E_G^b (φ ∧ X)`. The four-state structure `fig1` of Figure 1 is the paper's reason for the
detour: the naive infinite conjunction `E_G^b φ ∧ (E_G^b)² φ ∧ ⋯` (`Naive`) holds at `s₁`
(`fig1_naive`), `E_G^{1/2} p` fails at `s₂` and `s₃` (`fig1_everyoneProb`), and so the
conjunction is not a solution of the equation (`fig1_naive_not_fixedPoint`) while the
paper's `C_G^{1/2} p` is empty (`fig1_commonProb`).

## Implementation notes

* Propositions are sets of states and `w_i(φ) ≥ b` reads `μ_{i,s}` on the set; since
  `μ_{i,s}` vanishes off the sample space, this is the paper's `μ_{i,s}(S_{i,s}(φ))`
  (`prob_inter_sample`). The paper's inner measures for nonmeasurable sets are not modelled:
  mathlib evaluates every set by outer measure, and the one result that needs measurability,
  the fixed-point direction of Lemma 5.1 (continuity from above), assumes a discrete
  σ-algebra, the paper's MEAS in the finite case. Thresholds are real; the paper's rational
  coefficients embed.
* The group operators take the paper's `K_i^b φ = K_i(w_i(φ) ≥ b)` literally: `E_G^b φ` asks
  each member to know their probability formula, not merely to satisfy it; the two coincide
  under `SDP`, as in Figure 1.
* `fig1` is built from `Kernel.ofWeights` over natural-number weights, so that every
  threshold comparison reduces to a decidable inequality between weight sums
  (`fig1_atLeast_iff`) and the four-state facts are decided.
* Footnote 13's alternative equation `X ⇔ E_G^b φ ∧ E_G^b X` (Monderer and Samet), of which
  the naive conjunction is a solution, is not formalized.

## References

* [fagin-halpern-1994]
* [fagin-halpern-moses-vardi-1995]
-/

@[expose] public section

namespace FaginHalpern1994

open MeasureTheory ModalLogic ProbabilityTheory SetRel
open scoped ENNReal

/-- A Kripke structure for knowledge and probability `(S, π, 𝒦₁, …, 𝒦ₙ, 𝒫)`: accessibility
relations and, for each agent at each state, a probability space on a sample space of states.
The valuation `π` is the ambient `Set W`. -/
structure KripkeProb (E W : Type*) [MeasurableSpace W] where
  /-- Agent `i` considers `t` possible at `s`. -/
  access : E → SetRel W W
  /-- The sample space `S_{i,s}`. -/
  sample : E → W → Set W
  /-- The probability measure `μ_{i,s}`. -/
  prob : E → W → Measure W
  isProbabilityMeasure : ∀ i s, IsProbabilityMeasure (prob i s)
  /-- `μ_{i,s}` is carried by the sample space. -/
  prob_compl_sample : ∀ i s, prob i s (sample i s)ᶜ = 0

namespace KripkeProb

variable {E W : Type*} [MeasurableSpace W] {M : KripkeProb E W} {i : E} {s t : W}
  {b : ℝ} {φ ψ : Set W} {G : Set E}

instance (M : KripkeProb E W) (i : E) (s : W) : IsProbabilityMeasure (M.prob i s) :=
  M.isProbabilityMeasure i s

theorem prob_inter_sample (M : KripkeProb E W) (i : E) (s : W) (φ : Set W) :
    M.prob i s (φ ∩ M.sample i s) = M.prob i s φ :=
  measure_inter_conull (M.prob_compl_sample i s)

/-- The probability formula `w_i(φ) ≥ b`. -/
def AtLeast (M : KripkeProb E W) (b : ℝ) (i : E) (φ : Set W) : Set W :=
  {s | b ≤ (M.prob i s).real φ}

theorem AtLeast.mono (h : φ ⊆ ψ) : M.AtLeast b i φ ⊆ M.AtLeast b i ψ :=
  λ _ hs => hs.trans (measureReal_mono h)

/-! ### Conditions relating knowledge and probability -/

/-- CONS: the sample space lies within the states the agent considers possible. -/
def CONS (M : KripkeProb E W) : Prop := ∀ i s, M.sample i s ⊆ {t | s ~[M.access i] t}

/-- OBJ: all agents have the same probability space at each state. -/
def OBJ (M : KripkeProb E W) : Prop :=
  ∀ i j s, M.sample i s = M.sample j s ∧ M.prob i s = M.prob j s

/-- SDP: the probability space is determined by the agent's information cell. -/
def SDP (M : KripkeProb E W) : Prop :=
  ∀ i s t, s ~[M.access i] t → M.sample i s = M.sample i t ∧ M.prob i s = M.prob i t

/-- UNIF: the probability space is the same at every state of the sample space. -/
def UNIF (M : KripkeProb E W) : Prop :=
  ∀ i s t, t ∈ M.sample i s → M.sample i s = M.sample i t ∧ M.prob i s = M.prob i t

theorem UNIF.of_cons_sdp (hc : M.CONS) (hs : M.SDP) : M.UNIF :=
  λ i s t ht => hs i s t (hc i s ht)

theorem real_eq_one_of_sample_subset (h : M.sample i s ⊆ φ) : (M.prob i s).real φ = 1 := by
  have : M.prob i s φ = 1 := le_antisymm prob_le_one <| calc
    (1 : ℝ≥0∞) = M.prob i s Set.univ := measure_univ.symm
    _ ≤ M.prob i s (M.sample i s) + M.prob i s (M.sample i s)ᶜ := measure_univ_le_add_compl _
    _ = M.prob i s (M.sample i s) := by rw [M.prob_compl_sample, add_zero]
    _ ≤ M.prob i s φ := measure_mono h
  simp [measureReal_def, this]

theorem real_eq_zero_of_subset_compl_sample (h : φ ⊆ (M.sample i s)ᶜ) :
    (M.prob i s).real φ = 0 := by
  simp [measureReal_def, measure_mono_null h (M.prob_compl_sample i s)]

theorem real_eq_one_of_knows (hc : M.CONS) (h : s ∈ (M.access i).core φ) :
    (M.prob i s).real φ = 1 :=
  real_eq_one_of_sample_subset fun _ ht ↦ h (hc i s ht)

theorem UNIF.mem_atLeast_iff (hu : M.UNIF) (ht : t ∈ M.sample i s) :
    t ∈ M.AtLeast b i φ ↔ s ∈ M.AtLeast b i φ := by
  simp only [AtLeast, Set.mem_ofPred_eq, (hu i s t ht).2]

theorem UNIF.real_atLeast_eq_one (hu : M.UNIF) (hs : s ∈ M.AtLeast b i φ) :
    (M.prob i s).real (M.AtLeast b i φ) = 1 :=
  real_eq_one_of_sample_subset λ _ ht => (hu.mem_atLeast_iff ht).2 hs

theorem UNIF.real_compl_atLeast_eq_one (hu : M.UNIF) (hs : s ∉ M.AtLeast b i φ) :
    (M.prob i s).real (M.AtLeast b i φ)ᶜ = 1 :=
  real_eq_one_of_sample_subset λ _ ht h => hs ((hu.mem_atLeast_iff ht).1 h)

theorem UNIF.real_atLeast_eq_zero (hu : M.UNIF) (hs : s ∉ M.AtLeast b i φ) :
    (M.prob i s).real (M.AtLeast b i φ) = 0 :=
  real_eq_zero_of_subset_compl_sample λ _ ht hts => hs ((hu.mem_atLeast_iff hts).1 ht)

theorem SDP.mem_atLeast_iff (hs : M.SDP) (h : s ~[M.access i] t) :
    t ∈ M.AtLeast b i φ ↔ s ∈ M.AtLeast b i φ := by
  simp only [AtLeast, Set.mem_ofPred_eq, (hs i s t h).2]

theorem SDP.knows_atLeast (hsdp : M.SDP) (h : s ∈ M.AtLeast b i φ) :
    s ∈ (M.access i).core (M.AtLeast b i φ) :=
  λ _ ht => (hsdp.mem_atLeast_iff ht).2 h

theorem SDP.knows_compl_atLeast (hsdp : M.SDP) (h : s ∉ M.AtLeast b i φ) :
    s ∈ (M.access i).core (M.AtLeast b i φ)ᶜ :=
  λ _ ht h' => h ((hsdp.mem_atLeast_iff ht).1 h')

theorem UNIF.miller (hu : M.UNIF) (b : ℝ) (i : E) (φ : Set W) (s : W) :
    b * (M.prob i s).real (M.AtLeast b i φ) ≤ (M.prob i s).real φ := by
  by_cases hs : s ∈ M.AtLeast b i φ
  · rw [hu.real_atLeast_eq_one hs, mul_one]; exact hs
  · rw [hu.real_atLeast_eq_zero hs, mul_zero]; exact measureReal_nonneg

/-! ### Probabilistic common knowledge -/

/-- `E_G^b φ`: every member of `G` knows that their probability of `φ` is at least `b`. -/
def EveryoneProb (M : KripkeProb E W) (G : Set E) (b : ℝ) (φ : Set W) : Set W :=
  {s | ∀ i ∈ G, s ∈ (M.access i).core (M.AtLeast b i φ)}

theorem EveryoneProb.mono (h : φ ⊆ ψ) : M.EveryoneProb G b φ ⊆ M.EveryoneProb G b ψ :=
  fun _ hs i hi _ ht ↦ AtLeast.mono h (hs i hi ht)

theorem everyoneProb_empty [∀ i, (M.access i).IsRefl] (hG : G.Nonempty) (hb : 0 < b) :
    M.EveryoneProb G b ∅ = ∅ := by
  obtain ⟨i, hi⟩ := hG
  refine Set.eq_empty_of_forall_notMem λ s hs => hb.not_ge ?_
  have h1 : b ≤ (M.prob i s).real ∅ := hs i hi ((M.access i).refl s)
  simpa using h1

/-- The operator `X ↦ E_G^b (φ ∩ X)` whose greatest fixed point is `C_G^b φ`. -/
def everyoneProbHom (M : KripkeProb E W) (G : Set E) (b : ℝ) (φ : Set W) :
    Set W →o Set W :=
  ⟨λ X => M.EveryoneProb G b (φ ∩ X),
    λ _ _ h => EveryoneProb.mono (Set.inter_subset_inter_right _ h)⟩

/-- The iterates `(F_G^b)^k φ`: `(F_G^b)^0 φ = true` and
`(F_G^b)^{k+1} φ = E_G^b(φ ∧ (F_G^b)^k φ)`. -/
def F (M : KripkeProb E W) (G : Set E) (b : ℝ) (φ : Set W) : ℕ → Set W
  | 0 => Set.univ
  | k + 1 => M.EveryoneProb G b (φ ∩ M.F G b φ k)

/-- `C_G^b φ`: `(F_G^b)^k φ` for all `k ≥ 1`. -/
def CommonProb (M : KripkeProb E W) (G : Set E) (b : ℝ) (φ : Set W) : Set W :=
  ⋂ k, M.F G b φ (k + 1)

/-- The naive infinite conjunction `E_G^b φ ∧ (E_G^b)² φ ∧ ⋯`. -/
def Naive (M : KripkeProb E W) (G : Set E) (b : ℝ) (φ : Set W) : Set W :=
  ⋂ k, (M.EveryoneProb G b)^[k + 1] φ

theorem F_antitone (M : KripkeProb E W) (G : Set E) (b : ℝ) (φ : Set W) :
    Antitone (M.F G b φ) := by
  refine antitone_nat_of_succ_le λ k => ?_
  induction k with
  | zero => exact Set.subset_univ _
  | succ k ih => exact EveryoneProb.mono (Set.inter_subset_inter_right _ ih)

theorem commonProb_subset_F (M : KripkeProb E W) (G : Set E) (b : ℝ) (φ : Set W) (k : ℕ) :
    M.CommonProb G b φ ⊆ M.F G b φ k :=
  (Set.iInter_subset _ k).trans (M.F_antitone G b φ (Nat.le_succ k))

theorem subset_commonProb {X : Set W} (h : X ⊆ M.EveryoneProb G b (φ ∩ X)) :
    X ⊆ M.CommonProb G b φ := by
  refine Set.subset_iInter λ k => ?_
  induction k with
  | zero => exact h.trans (EveryoneProb.mono (Set.inter_subset_inter_right _ (Set.subset_univ _)))
  | succ k ih => exact h.trans (EveryoneProb.mono (Set.inter_subset_inter_right _ ih))

theorem everyoneProb_inter_commonProb_subset :
    M.EveryoneProb G b (φ ∩ M.CommonProb G b φ) ⊆ M.CommonProb G b φ :=
  Set.subset_iInter λ k =>
    EveryoneProb.mono (Set.inter_subset_inter_right _ (M.commonProb_subset_F G b φ k))

theorem commonProb_subset_everyoneProb_inter [DiscreteMeasurableSpace W] :
    M.CommonProb G b φ ⊆ M.EveryoneProb G b (φ ∩ M.CommonProb G b φ) := by
  intro s hs i hi t ht
  have hk : ∀ k, ENNReal.ofReal b ≤ M.prob i t (φ ∩ M.F G b φ (k + 1)) := λ k =>
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
      (Set.mem_iInter.1 hs (k + 1) i hi ht)
  have hanti : Antitone λ k => φ ∩ M.F G b φ (k + 1) :=
    λ _ _ h => Set.inter_subset_inter_right _ (M.F_antitone G b φ (Nat.succ_le_succ h))
  show b ≤ (M.prob i t).real (φ ∩ ⋂ k, M.F G b φ (k + 1))
  rw [measureReal_def, Set.inter_iInter,
    hanti.measure_iInter (λ _ => MeasurableSet.of_discrete.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
  have hfin : (⨅ k, M.prob i t (φ ∩ M.F G b φ (k + 1))) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top _ _) (iInf_le _ 0)
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 (le_iInf hk)

/-- Lemma 5.1: `C_G^b φ` is the greatest fixed point of `X ⇔ E_G^b(φ ∧ X)`. -/
theorem commonProb_eq_gfp [DiscreteMeasurableSpace W] (M : KripkeProb E W) (G : Set E) (b : ℝ)
    (φ : Set W) : M.CommonProb G b φ = (M.everyoneProbHom G b φ).gfp :=
  le_antisymm ((M.everyoneProbHom G b φ).le_gfp commonProb_subset_everyoneProb_inter)
    ((M.everyoneProbHom G b φ).gfp_le λ _ hX => subset_commonProb hX)

end KripkeProb

/-! ### Figure 1

Four states `s₁, …, s₄` (here `0, …, 3`), agent 1 unable to distinguish `s₁` from `s₂` and
`s₃` from `s₄`, agent 2 unable to distinguish `s₁` from `s₃` and `s₂` from `s₄`, `p` true at
`s₂` and `s₃`. The structure satisfies SDP: agent 1 at `s₁, s₂` puts `1/2` on each of `s₁,
s₂`, agent 2 at `s₁, s₃` puts `1/2` on each of `s₁, s₃`, and both put probability one on `s₄`
at the states of their other cell. -/

section Figure1

open KripkeProb

/-- Agent `i`'s information cell of state `s`. -/
def fig1Cell (i : Fin 2) (s : Fin 4) : Fin 2 :=
  match i.val, s.val with
  | 0, 0 | 0, 1 => 0
  | 0, _ => 1
  | _, 0 | _, 2 => 0
  | _, _ => 1

/-- The weights of `μ_{i,s}` over the states. -/
def fig1Weight (i : Fin 2) (s : Fin 4) (t : Fin 4) : ℕ :=
  match i.val, s.val, t.val with
  | 0, 0, 0 | 0, 0, 1 | 0, 1, 0 | 0, 1, 1 => 1
  | 0, 2, 3 | 0, 3, 3 => 1
  | 1, 0, 0 | 1, 0, 2 | 1, 2, 0 | 1, 2, 2 => 1
  | 1, 1, 3 | 1, 3, 3 => 1
  | _, _, _ => 0

/-- `p` of Figure 1, true at `s₂` and `s₃`. -/
def fig1P : Set (Fin 4) := {t | t = 1 ∨ t = 2}

theorem fig1Weight_pos : ∀ i s, 0 < ∑ t, fig1Weight i s t := by decide

private theorem fig1Weight_eq_zero :
    ∀ i s t, fig1Cell i s ≠ fig1Cell i t → fig1Weight i s t = 0 := by
  decide

/-- The Kripke structure `M` of Figure 1. -/
noncomputable def fig1 : KripkeProb (Fin 2) (Fin 4) where
  access i := {p | fig1Cell i p.1 = fig1Cell i p.2}
  sample i s := {t | fig1Cell i s = fig1Cell i t}
  prob i s := Kernel.ofWeights (λ s t => (fig1Weight i s t : ℝ≥0∞)) s
  isProbabilityMeasure i s :=
    have := Kernel.isMarkovKernel_ofWeights (w := λ s t => (fig1Weight i s t : ℝ≥0∞))
      (λ s => (Finset.exists_ne_zero_of_sum_ne_zero (fig1Weight_pos i s).ne').imp
        λ t ht => by simpa using ht) (λ _ _ => ENNReal.natCast_ne_top _)
    inferInstance
  prob_compl_sample i s :=
    measure_mono_null (λ t ht => by simpa using fig1Weight_eq_zero i s t ht)
      (Kernel.ofWeights_apply_setOf_eq_zero _ s)

instance (i : Fin 2) : (fig1.access i).IsRefl := ⟨fun _ ↦ rfl⟩

theorem fig1_atLeast_iff (i : Fin 2) (t : Fin 4) (p : Fin 4 → Prop) [DecidablePred p] :
    t ∈ fig1.AtLeast (1 / 2) i {u | p u} ↔
      ∑ u, fig1Weight i t u ≤ 2 * ∑ u with p u, fig1Weight i t u := by
  have hpos : (0 : ℝ) < ∑ u, (fig1Weight i t u : ℝ) := by exact_mod_cast fig1Weight_pos i t
  show (1 / 2 : ℝ) ≤ (Kernel.ofWeights (λ s t => (fig1Weight i s t : ℝ≥0∞)) t).real {u | p u} ↔ _
  rw [Kernel.ofWeights_real_setOf _ t (λ _ => ENNReal.natCast_ne_top _) p]
  simp only [ENNReal.toReal_natCast]
  rw [le_div_iff₀ hpos, one_div, inv_mul_le_iff₀ two_pos]
  exact_mod_cast Iff.rfl

theorem fig1_everyoneProb : fig1.EveryoneProb Set.univ (1 / 2) fig1P = {0} := by
  ext s
  simp only [EveryoneProb, Set.mem_ofPred_eq, Set.mem_univ, true_implies, mem_core, fig1P,
    fig1_atLeast_iff, Set.mem_singleton_iff]
  show (∀ i t, fig1Cell i s = fig1Cell i t → _) ↔ _
  revert s; decide

theorem fig1_everyoneProb_singleton : fig1.EveryoneProb Set.univ (1 / 2) {0} = {0} := by
  show fig1.EveryoneProb Set.univ (1 / 2) {u | u = 0} = {0}
  ext s
  simp only [EveryoneProb, Set.mem_ofPred_eq, Set.mem_univ, true_implies, mem_core,
    fig1_atLeast_iff, Set.mem_singleton_iff]
  show (∀ i t, fig1Cell i s = fig1Cell i t → _) ↔ _
  revert s; decide

private theorem fig1P_inter_singleton : fig1P ∩ {0} = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 λ t => by
    simp only [fig1P, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    revert t; decide

theorem fig1_naive : fig1.Naive Set.univ (1 / 2) fig1P = {0} := by
  have h : ∀ k, (fig1.EveryoneProb Set.univ (1 / 2))^[k + 1] fig1P = {0} := by
    intro k
    induction k with
    | zero => exact fig1_everyoneProb
    | succ k ih => rw [Function.iterate_succ_apply', ih, fig1_everyoneProb_singleton]
  unfold Naive
  rw [Set.iInter_congr h, Set.iInter_const]

theorem fig1_naive_not_fixedPoint :
    ¬ fig1.Naive Set.univ (1 / 2) fig1P ⊆
      fig1.EveryoneProb Set.univ (1 / 2) (fig1P ∩ fig1.Naive Set.univ (1 / 2) fig1P) := by
  rw [fig1_naive, fig1P_inter_singleton, everyoneProb_empty Set.univ_nonempty one_half_pos]
  simp

theorem fig1_commonProb : fig1.CommonProb Set.univ (1 / 2) fig1P = ∅ := by
  refine Set.eq_empty_of_subset_empty ((fig1.commonProb_subset_F _ _ _ 2).trans ?_)
  show fig1.EveryoneProb _ _ (fig1P ∩ fig1.EveryoneProb _ _ (fig1P ∩ Set.univ)) ⊆ ∅
  rw [Set.inter_univ, fig1_everyoneProb, fig1P_inter_singleton,
    everyoneProb_empty Set.univ_nonempty one_half_pos]

end Figure1

end FaginHalpern1994
