module

public import Linglib.Pragmatics.DecisionTheoretic.Basic
public import Linglib.Semantics.Focus.Particles

/-!
# Merin (1999): Information, Relevance, and Social Decisionmaking

This file formalizes the applications of Decision-Theoretic Semantics in [merin-1999-relevance]
to *or*, *but*, *even*, and *also*. The framework (contexts, relevance, issue-conditional
independence, Fact 5, Theorem 6a) is `Pragmatics/DecisionTheoretic/Basic.lean`.

*Scalar implicature.* Hypothesis 3 licenses *X if not indeed Y* in a context when Y is more
relevant than X, and X positively so, to one side of the issue (`IfNotIndeed`). When A and B
are independent on each side of the issue and finitely confirm it (`IndepConfirmers`, the
antecedent of Theorem 6), Theorem 6a makes the conjunction more relevant than either disjunct
and than the disjunction, so *A (or B), if not indeed A and B* is licensed (Prediction 2,
`IndepConfirmers.ifNotIndeed_inter`). Theorem 6b's non-derivabilities are countermodels: the
exclusive disjunction can be negatively relevant (`exists_negRelevant_symmDiff`) or not
(`exists_not_negRelevant_symmDiff`), and the disjunction can be as relevant as a disjunct, which
blocks *A or B, if not indeed A* (Prediction 1, `exists_not_ifNotIndeed_union`).

*But and even.* Hypothesis 4 (`ButFelicitous`) makes A an argument for the issue and B and A∧B
arguments against it. Hypothesis 5 (`EvenFelicitous`) is the scalar presupposition of *even*
(`Focus.evenPresup`) with relevance in place of likelihood; by Fact 2 the most
relevant alternative is the one whose truth would be most surprising if ¬H rather than H were
accepted, Merin's reconciliation of argumentative value with [francescotti-1995]'s surprise and
against [kay-1990]'s informativeness. With one issue per reading, the two hypotheses clash on
the sign of B (Prediction 3, `not_butFelicitous_and_evenFelicitous`). Under issue-conditional
independence, A and B are H-contrary iff B is unexpected given A (Theorem 8,
`cond_lt_iff_hContrary`). The default issue of *A but B* is ¬B, where independence holds
automatically (Theorem 9) and the basic properties of *but* follow (Theorem 10). Non-negative
instantial relevance then excludes *Qa but Qb* (Corollary 11), Harris's subject-predicate
asymmetry.

*Also.* A proposition is presupposed when conditioning on it changes nothing (Definition 12),
equivalently when it has probability one (`isPresupposed_iff`); it is then irrelevant to every
issue and factors out of conjunctions (Fact 17). The antecedent of *also* must have spent its
relevance in becoming presupposed (Definition 13, Hypothesis 8), so it cannot be the focus's own
instance (Corollary 15), cannot be properly accommodated (Partial Definition 14), and lacks prima
facie causal responsibility for its host (Corollary 16, Prediction 4).

## Implementation notes

- Relevance statements are on `bayesFactor` in `ℝ≥0∞`: r > 0 is `1 < bayesFactor`, finitude of
  relevance is `bayesFactor ≠ ⊤`, and Merin's sgn(r) is `compare (bayesFactor ctx e) 1`.
- The earlier context i − k of Definition 13 is a second `Context` over the same issue; that it
  is the last one before D became presupposed is not modelled.
- Theorem 6b's countermodels are counting priors on small world types.

## TODO

- Theorem 6a's clause that the disjunction is more relevant than the exclusive disjunction is
  not formalized.
- Definition 7, Definition 8 with Hypothesis 1 (claims and implicatures as relevance cones),
  Fact 4, Theorem 7, and Theorems 12 and 13 with Corollary 14 are not formalized.

## References

* [merin-1999-relevance]
* [anscombre-ducrot-1977]
* [karttunen-peters-1979]
* [kay-1990]
* [francescotti-1995]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory DTS
open scoped ENNReal symmDiff

namespace Merin1999a

variable {W : Type*} [MeasurableSpace W]

/-! ### Scalar implicature -/

/-- The antecedent of Theorem 6: A and B independent conditionally on each side of the issue
(Definition 9) and each confirming H finitely, ∞ > r(A), r(B) > 0. -/
structure IndepConfirmers (ctx : Context W) (a b : Set W) : Prop where
  indep : CondIndepIssue ctx a b
  one_lt_left : posRelevant ctx a
  one_lt_right : posRelevant ctx b
  ne_top_left : bayesFactor ctx a ≠ ⊤
  ne_top_right : bayesFactor ctx b ≠ ⊤

private theorem cond_compl_ne_zero {ctx : Context W} {e : Set W} (hp : posRelevant ctx e)
    (ht : bayesFactor ctx e ≠ ⊤) : ctx.prior[|ctx.topicᶜ] e ≠ 0 := by
  intro h0
  rw [posRelevant, bayesFactor_def, h0] at hp
  rw [bayesFactor_def, h0] at ht
  rcases eq_or_ne (ctx.prior[|ctx.topic] e) 0 with hx | hx
  · simp [hx] at hp
  · exact ht (ENNReal.div_zero hx)

/-- The condition Hypothesis 3 places on a context for *X if not indeed Y*: X is positively
relevant, and Y more so, to H or to ¬H. The schema is acceptable iff every context in which X
and Y satisfy the Conditional Independence Presumption with finite relevance meets it. -/
def IfNotIndeed (ctx : Context W) (x y : Set W) : Prop :=
  (1 < bayesFactor ctx x ∧ bayesFactor ctx x < bayesFactor ctx y) ∨
    (1 < bayesFactor (swapIssue ctx) x ∧
      bayesFactor (swapIssue ctx) x < bayesFactor (swapIssue ctx) y)

/-- For independent finite confirmers A and B of H, *A (or B), if not indeed A and B* is licensed
(Prediction 2, Theorem 6a). -/
theorem IndepConfirmers.ifNotIndeed_inter {ctx : Context W} [IsFiniteMeasure ctx.prior]
    [ctx.Nondegenerate] {a b : Set W} (hbm : MeasurableSet b) (h : IndepConfirmers ctx a b) :
    IfNotIndeed ctx (a ∪ b) (a ∩ b) ∧ IfNotIndeed ctx a (a ∩ b) := by
  have ha := cond_compl_ne_zero h.one_lt_left h.ne_top_left
  have hb := cond_compl_ne_zero h.one_lt_right h.ne_top_right
  have hmax := h.indep.max_bayesFactor_lt_inter h.one_lt_left h.one_lt_right ha hb
  exact ⟨.inl ⟨h.indep.one_lt_bayesFactor_union hbm h.one_lt_left h.one_lt_right ha hb,
      (h.indep.bayesFactor_union_lt_max hbm h.one_lt_left h.one_lt_right ha hb).trans hmax⟩,
    .inl ⟨h.one_lt_left, (le_max_left _ _).trans_lt hmax⟩⟩

/-! #### Theorem 6b -/

/-- The worlds of the first countermodel: at `issue`, the only world where H holds, A and B both
hold; at `off a b`, A holds iff `a` and B iff `b`. -/
inductive World₁ where
  | issue
  | off (a b : Bool)
  deriving DecidableEq, Fintype

instance : MeasurableSpace World₁ := ⊤
instance : DiscreteMeasurableSpace World₁ := ⟨fun _ ↦ trivial⟩

/-- Whether A holds at a world of the first countermodel. -/
def World₁.a : World₁ → Bool
  | .issue => true
  | .off a _ => a

/-- Whether B holds at a world of the first countermodel. -/
def World₁.b : World₁ → Bool
  | .issue => true
  | .off _ b => b

private abbrev H₁ : Set World₁ := {w | w = .issue}
private abbrev A₁ : Set World₁ := {w | w.a}
private abbrev B₁ : Set World₁ := {w | w.b}

private theorem ncard₁ :
    H₁.ncard = 1 ∧ H₁ᶜ.ncard = 4 ∧ (H₁ ∩ A₁).ncard = 1 ∧ (H₁ᶜ ∩ A₁).ncard = 2 ∧
      (H₁ ∩ B₁).ncard = 1 ∧ (H₁ᶜ ∩ B₁).ncard = 2 ∧ (H₁ ∩ (A₁ ∩ B₁)).ncard = 1 ∧
      (H₁ᶜ ∩ (A₁ ∩ B₁)).ncard = 1 ∧ (H₁ ∩ (A₁ ∆ B₁)).ncard = 0 ∧
      (H₁ᶜ ∩ (A₁ ∆ B₁)).ncard = 2 := by
  simp only [Set.symmDiff_def, Set.ncard_eq_toFinset_card']
  decide

private theorem indepConfirmers₁ :
    IndepConfirmers ⟨H₁, .of_discrete, .count⟩ A₁ B₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩ := ncard₁
  have ta : bayesFactor ⟨H₁, .of_discrete, .count⟩ A₁ ≠ ⊤ :=
    bayesFactor_count_ne_top ⟨.off true false, by simp [World₁.a]⟩
  have tb : bayesFactor ⟨H₁, .of_discrete, .count⟩ B₁ ≠ ⊤ :=
    bayesFactor_count_ne_top ⟨.off false true, by simp [World₁.b]⟩
  refine ⟨condIndepIssue_count_iff.mpr ⟨?_, ?_⟩, ?_, ?_, ta, tb⟩
  · rw [h7, h1, h3, h5]
  · rw [h8, h2, h4, h6]
  · rw [posRelevant_iff_one_lt_toReal ta, toReal_bayesFactor_count, h1, h2, h3, h4]
    norm_num
  · rw [posRelevant_iff_one_lt_toReal tb, toReal_bayesFactor_count, h1, h2, h5, h6]
    norm_num

/-- The exclusive disjunction of independent finite confirmers can disconfirm H, so the first clause
of Theorem 6b is not derivable. -/
theorem exists_negRelevant_symmDiff :
    ∃ (ctx : Context World₁) (a b : Set World₁),
      IndepConfirmers ctx a b ∧ negRelevant ctx (a ∆ b) := by
  refine ⟨_, _, _, indepConfirmers₁, ?_⟩
  obtain ⟨h1, h2, -, -, -, -, -, -, h9, h10⟩ := ncard₁
  rw [negRelevant_iff_toReal_lt_one (bayesFactor_count_ne_top
      ⟨.off true false, by simp [Set.mem_symmDiff, World₁.a, World₁.b]⟩),
    toReal_bayesFactor_count, h1, h2, h9, h10]
  norm_num

/-- The worlds of the second countermodel: at `issue a`, where H holds, A holds iff `a` and B
holds; at `off i b`, A holds iff `i = 0` and B iff `b`. -/
inductive World₂ where
  | issue (a : Bool)
  | off (i : Fin 3) (b : Bool)
  deriving DecidableEq, Fintype

instance : MeasurableSpace World₂ := ⊤
instance : DiscreteMeasurableSpace World₂ := ⟨fun _ ↦ trivial⟩

/-- Whether H holds at a world of the second countermodel. -/
def World₂.h : World₂ → Bool
  | .issue _ => true
  | .off _ _ => false

/-- Whether A holds at a world of the second countermodel. -/
def World₂.a : World₂ → Bool
  | .issue a => a
  | .off i _ => i = 0

/-- Whether B holds at a world of the second countermodel. -/
def World₂.b : World₂ → Bool
  | .issue _ => true
  | .off _ b => b

private abbrev H₂ : Set World₂ := {w | w.h}
private abbrev A₂ : Set World₂ := {w | w.a}
private abbrev B₂ : Set World₂ := {w | w.b}

private theorem ncard₂ :
    H₂.ncard = 2 ∧ H₂ᶜ.ncard = 6 ∧ (H₂ ∩ A₂).ncard = 1 ∧ (H₂ᶜ ∩ A₂).ncard = 2 ∧
      (H₂ ∩ B₂).ncard = 2 ∧ (H₂ᶜ ∩ B₂).ncard = 3 ∧ (H₂ ∩ (A₂ ∩ B₂)).ncard = 1 ∧
      (H₂ᶜ ∩ (A₂ ∩ B₂)).ncard = 1 ∧ (H₂ ∩ (A₂ ∪ B₂)).ncard = 2 ∧
      (H₂ᶜ ∩ (A₂ ∪ B₂)).ncard = 4 ∧ (H₂ ∩ (A₂ ∆ B₂)).ncard = 1 ∧
      (H₂ᶜ ∩ (A₂ ∆ B₂)).ncard = 3 := by
  simp only [Set.symmDiff_def, Set.ncard_eq_toFinset_card']
  decide

private noncomputable abbrev ctx₂ : Context World₂ := ⟨H₂, .of_discrete, .count⟩

private theorem ne_top₂ {e : Set World₂} (h : (H₂ᶜ ∩ e).Nonempty) : bayesFactor ctx₂ e ≠ ⊤ :=
  bayesFactor_count_ne_top h

private theorem indepConfirmers₂ : IndepConfirmers ctx₂ A₂ B₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := ncard₂
  have ta := ne_top₂ (e := A₂) ⟨.off 0 false, by simp [World₂.h, World₂.a]⟩
  have tb := ne_top₂ (e := B₂) ⟨.off 1 true, by simp [World₂.h, World₂.b]⟩
  refine ⟨condIndepIssue_count_iff.mpr ⟨?_, ?_⟩, ?_, ?_, ta, tb⟩
  · rw [h7, h1, h3, h5]
  · rw [h8, h2, h4, h6]
  · rw [posRelevant_iff_one_lt_toReal ta, toReal_bayesFactor_count, h1, h2, h3, h4]
    norm_num
  · rw [posRelevant_iff_one_lt_toReal tb, toReal_bayesFactor_count, h1, h2, h5, h6]
    norm_num

/-- Theorem 6b, second clause: that the exclusive disjunction of independent finite confirmers
disconfirms H is not derivable either. In the second countermodel it is irrelevant. -/
theorem exists_not_negRelevant_symmDiff :
    ∃ (ctx : Context World₂) (a b : Set World₂),
      IndepConfirmers ctx a b ∧ ¬ negRelevant ctx (a ∆ b) := by
  refine ⟨_, _, _, indepConfirmers₂, ?_⟩
  obtain ⟨h1, h2, -, -, -, -, -, -, -, -, h11, h12⟩ := ncard₂
  rw [negRelevant_iff_toReal_lt_one
      (ne_top₂ ⟨.off 0 false, by simp [Set.mem_symmDiff, World₂.h, World₂.a, World₂.b]⟩),
    toReal_bayesFactor_count, h1, h2, h11, h12]
  norm_num

/-- Independent finite confirmers need not license *A or B, if not indeed A*, since neither
condition of Hypothesis 3 need hold (Prediction 1, Theorem 6b). -/
theorem exists_not_ifNotIndeed_union :
    ∃ (ctx : Context World₂) (a b : Set World₂),
      IndepConfirmers ctx a b ∧ ¬ IfNotIndeed ctx (a ∪ b) a := by
  refine ⟨_, _, _, indepConfirmers₂, ?_⟩
  obtain ⟨h1, h2, h3, h4, -, -, -, -, h9, h10, -⟩ := ncard₂
  have tu := ne_top₂ (e := A₂ ∪ B₂) ⟨.off 0 false, by simp [World₂.h, World₂.a]⟩
  have ta := ne_top₂ (e := A₂) ⟨.off 0 false, by simp [World₂.h, World₂.a]⟩
  have hsu : (bayesFactor (swapIssue ctx₂) (A₂ ∪ B₂)).toReal = 2 / 3 := by
    rw [show swapIssue ctx₂ = ⟨H₂ᶜ, .of_discrete, .count⟩ from rfl, toReal_bayesFactor_count,
      compl_compl, h1, h2, h9, h10]
    norm_num
  have hsu' : bayesFactor (swapIssue ctx₂) (A₂ ∪ B₂) ≠ ⊤ := by
    intro h; rw [h] at hsu; norm_num at hsu
  rintro (⟨-, h⟩ | ⟨h, -⟩)
  · rw [← ENNReal.toReal_lt_toReal tu ta, toReal_bayesFactor_count, toReal_bayesFactor_count,
      h1, h2, h3, h4, h9, h10] at h
    norm_num at h
  · rw [← ENNReal.toReal_lt_toReal ENNReal.one_ne_top hsu', hsu] at h
    norm_num at h

/-! ### *But* and *even* -/

/-- Hypothesis 4: *A but B* is felicitous only if, for the issue H, A confirms H while B and A∧B
disconfirm it. -/
def ButFelicitous (ctx : Context W) (a b : Set W) : Prop :=
  posRelevant ctx a ∧ negRelevant ctx b ∧ negRelevant ctx (a ∩ b)

/-- Hypothesis 5: *A CONJ even(B)* with VP-focus is felicitous only if, for an issue H other than
B, A confirms H and B is more relevant to H than A: the scalar presupposition of *even* with
relevance for likelihood, over the one alternative A. -/
def EvenFelicitous (ctx : Context W) (a b : Set W) : Prop :=
  ctx.topic ≠ b ∧ posRelevant ctx a ∧
    Focus.evenPresup (fun e ↦ OrderDual.toDual (bayesFactor ctx e)) b {a}

theorem not_butFelicitous_and_evenFelicitous (ctx : Context W) (a b : Set W) :
    ¬ (ButFelicitous ctx a b ∧ EvenFelicitous ctx a b) := by
  rintro ⟨⟨-, hb, -⟩, -, ha, he⟩
  exact lt_irrefl _ ((ha.trans (OrderDual.toDual_lt_toDual.mp (he a rfl))).trans hb)

/-- Under issue-conditional independence, B is unexpected given A iff A and B are H-contrary
(Theorem 8). -/
theorem cond_lt_iff_hContrary (ctx : Context W) [IsProbabilityMeasure ctx.prior]
    [ctx.Nondegenerate] {a b : Set W} (ham : MeasurableSet a) (hcip : CondIndepIssue ctx a b)
    (ha0 : ctx.prior a ≠ 0) (hb0 : ctx.prior b ≠ 0) :
    ctx.prior[|a] b < ctx.prior b ↔ hContrary ctx a b := by
  have hH : ctx.prior ctx.topic ≠ 0 := Context.Nondegenerate.topic_ne_zero
  have hNH : ctx.prior ctx.topicᶜ ≠ 0 := Context.Nondegenerate.compl_ne_zero
  rw [hContrary, posRelevant_iff_real_cross, negRelevant_iff_real_cross ctx hb0,
    negRelevant_iff_real_cross ctx ha0, posRelevant_iff_real_cross]
  set μ := ctx.prior
  set H := ctx.topic
  have hHm : MeasurableSet H := ctx.topicMeasurable
  have hsplit (e : Set W) : μ.real e = μ.real (H ∩ e) + μ.real (Hᶜ ∩ e) := by
    rw [← measureReal_inter_add_sdiff (s := e) hHm, Set.sdiff_eq, Set.inter_comm e,
      Set.inter_comm e]
  have hcip' (s : Set W) (hs : MeasurableSet s) (θ : Bool) (hθ : ctx.conditional θ = μ[|s]) :
      μ.real (s ∩ (a ∩ b)) / μ.real s =
        μ.real (s ∩ a) / μ.real s * (μ.real (s ∩ b) / μ.real s) := by
    rw [← cond_real_apply μ hs, ← cond_real_apply μ hs, ← cond_real_apply μ hs, ← hθ]
    exact (hcip θ).measureReal_inter_eq_mul
  have hcipH' := hcip' H hHm true rfl
  have hcipNH' := hcip' Hᶜ hHm.compl false rfl
  rw [← ENNReal.toReal_lt_toReal (measure_ne_top μ[|a] b) (measure_ne_top μ b),
    ← measureReal_def, ← measureReal_def, cond_real_apply μ ham b,
    div_lt_iff₀ (show 0 < μ.real a from ENNReal.toReal_pos ha0 (measure_ne_top μ a)),
    hsplit a, hsplit b,
    hsplit (a ∩ b)]
  set pH := μ.real H
  set pnH := μ.real Hᶜ
  set aH := μ.real (H ∩ a)
  set anH := μ.real (Hᶜ ∩ a)
  set bH := μ.real (H ∩ b)
  set bnH := μ.real (Hᶜ ∩ b)
  set abH := μ.real (H ∩ (a ∩ b))
  set abnH := μ.real (Hᶜ ∩ (a ∩ b))
  have hpH : 0 < pH := ENNReal.toReal_pos hH (measure_ne_top μ _)
  have hpnH : 0 < pnH := ENNReal.toReal_pos hNH (measure_ne_top μ _)
  have hsum : pH + pnH = 1 := by
    rw [measureReal_add_measureReal_compl hHm, probReal_univ]
  have hcipH : abH * pH = aH * bH := by
    field_simp at hcipH'
    linear_combination hcipH'
  have hcipNH : abnH * pnH = anH * bnH := by
    field_simp at hcipNH'
    linear_combination hcipNH'
  have hid : ((aH + anH) * (bH + bnH) - (abH + abnH)) * (pH * pnH) =
      (pnH * aH - pH * anH) * (pH * bnH - pnH * bH) := by
    linear_combination (-pnH) * hcipH + (-pH) * hcipNH + (aH * bH * pnH + anH * bnH * pH) * hsum
  have key : abH + abnH < (bH + bnH) * (aH + anH) ↔
      0 < (pnH * aH - pH * anH) * (pH * bnH - pnH * bH) := by
    rw [← hid, mul_pos_iff_of_pos_right (mul_pos hpH hpnH), sub_pos, mul_comm (bH + bnH)]
  rw [key, mul_pos_iff]
  constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  all_goals first
    | exact .inl ⟨by linarith, by linarith⟩
    | exact .inr ⟨by linarith, by linarith⟩

/-- The default context of *A but B*: the issue is ¬B, the special case of Hypothesis 4 that
[merin-1999-relevance] compares with [anscombre-ducrot-1977] and proposes as the default
interpretation. -/
abbrev defaultButCtx (μ : Measure W) (b : Set W) (hb : MeasurableSet b) : Context W :=
  ⟨bᶜ, hb.compl, μ⟩

-- Theorem 9
theorem condIndepIssue_defaultButCtx (μ : Measure W) [IsFiniteMeasure μ] {a b : Set W}
    (ham : MeasurableSet a) (hbm : MeasurableSet b) :
    CondIndepIssue (defaultButCtx μ b hbm) a b := by
  refine (condIndepIssue_iff _ ham hbm).mpr ⟨?_, ?_⟩
  · show μ[|bᶜ] (a ∩ b) = μ[|bᶜ] a * μ[|bᶜ] b
    rw [cond_apply hbm.compl, cond_apply hbm.compl, cond_apply hbm.compl,
      Set.inter_comm a b, ← Set.inter_assoc, Set.compl_inter_self, Set.empty_inter]
    simp
  · show μ[|bᶜᶜ] (a ∩ b) = μ[|bᶜᶜ] a * μ[|bᶜᶜ] b
    rw [compl_compl]
    rcases eq_or_ne (μ b) 0 with h0 | h0
    · simp [cond_eq_zero_of_meas_eq_zero h0]
    · rw [cond_apply_self h0 (measure_ne_top _ _), mul_one, Set.inter_comm, cond_inter_self hbm]

-- Theorem 10
theorem negRelevant_defaultButCtx (μ : Measure W) {b : Set W} (hbm : MeasurableSet b) :
    negRelevant (defaultButCtx μ b hbm) b := by
  show μ[|bᶜ] b / μ[|bᶜᶜ] b < 1
  rw [cond_apply hbm.compl, Set.compl_inter_self]
  simp

-- Theorem 10
theorem bayesFactor_lt_swapIssue_defaultButCtx (μ : Measure W) [IsFiniteMeasure μ]
    {a b : Set W} (hbm : MeasurableSet b) (hab : μ (a ∩ b) ≠ 0) :
    bayesFactor (defaultButCtx μ b hbm) a < bayesFactor (swapIssue (defaultButCtx μ b hbm)) b ∧
      bayesFactor (defaultButCtx μ b hbm) a <
        bayesFactor (swapIssue (defaultButCtx μ b hbm)) (a ∩ b) := by
  have hb : μ b ≠ 0 := fun h ↦ hab (measure_mono_null Set.inter_subset_right h)
  have hne : μ[|b] (a ∩ b) ≠ 0 := by
    rw [cond_apply hbm, Set.inter_comm, Set.inter_assoc, Set.inter_self]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hab
  have hfin : bayesFactor (defaultButCtx μ b hbm) a < ⊤ := by
    refine (bayesFactor_ne_top ?_).lt_top
    show μ[|bᶜᶜ] a ≠ 0
    rw [compl_compl, cond_apply hbm, Set.inter_comm]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hab
  have hnull : ∀ e ⊆ b, μ[|bᶜ] e = 0 := fun e he ↦ by
    rw [cond_apply hbm.compl, Set.disjoint_iff_inter_eq_empty.mp
      (disjoint_compl_left.mono_right he), measure_empty, mul_zero]
  simp only [bayesFactor_swapIssue, defaultButCtx, compl_compl,
    hnull b subset_rfl, hnull (a ∩ b) Set.inter_subset_right,
    ENNReal.div_zero (cond_apply_self hb (measure_ne_top _ _) ▸ one_ne_zero), ENNReal.div_zero hne]
  exact ⟨hfin, hfin⟩

-- Theorem 10, Theorem 8, Theorem 9
theorem cond_lt_of_posRelevant_defaultButCtx (μ : Measure W) [IsProbabilityMeasure μ]
    {a b : Set W} (ham : MeasurableSet a) (hbm : MeasurableSet b)
    (hpos : posRelevant (defaultButCtx μ b hbm) a) (hab : μ (a ∩ b) ≠ 0) :
    μ[|a] b < μ b := by
  have ha : μ a ≠ 0 := fun h ↦ hab (measure_mono_null Set.inter_subset_left h)
  have hb : μ b ≠ 0 := fun h ↦ hab (measure_mono_null Set.inter_subset_right h)
  have hbc : μ bᶜ ≠ 0 := fun h ↦ by
    simp [posRelevant, bayesFactor_def, cond_eq_zero_of_meas_eq_zero h] at hpos
  have : (defaultButCtx μ b hbm).Nondegenerate := ⟨hbc, by rwa [compl_compl]⟩
  exact (cond_lt_iff_hContrary _ ham (condIndepIssue_defaultButCtx μ ham hbm) ha hb).mpr
    (.inl ⟨hpos, negRelevant_defaultButCtx μ hbm⟩)

-- Theorem 10, Fact 5, Theorem 9
theorem bayesFactor_inter_defaultButCtx (μ : Measure W) [IsFiniteMeasure μ] {a b : Set W}
    (ham : MeasurableSet a) (hbm : MeasurableSet b) (hb : μ b ≠ 0) :
    bayesFactor (defaultButCtx μ b hbm) (a ∩ b) =
      bayesFactor (defaultButCtx μ b hbm) a * bayesFactor (defaultButCtx μ b hbm) b :=
  (condIndepIssue_defaultButCtx μ ham hbm).bayesFactor_inter <| by
    show μ[|bᶜᶜ] b ≠ 0
    rw [compl_compl, cond_apply_self hb (measure_ne_top _ _)]
    exact one_ne_zero

/-- Definition 10: the prior satisfies non-negative instantial relevance for a predicate Q when
no instance Qa makes another instance Qb less probable. -/
def NonnegInstantialRelevance {E : Type*} (μ : Measure W) (Q : E → Set W) : Prop :=
  ∀ i j, μ (Q j) ≤ μ[|Q i] (Q j)

-- Corollary 11, Theorem 8
theorem not_butFelicitous_of_nonnegInstantialRelevance {E : Type*} (ctx : Context W)
    [IsProbabilityMeasure ctx.prior] [ctx.Nondegenerate] {Q : E → Set W}
    (hQ : NonnegInstantialRelevance ctx.prior Q) {i j : E} (hm : MeasurableSet (Q i))
    (hcip : CondIndepIssue ctx (Q i) (Q j)) (hi : ctx.prior (Q i) ≠ 0)
    (hj : ctx.prior (Q j) ≠ 0) :
    ¬ ButFelicitous ctx (Q i) (Q j) := fun h ↦
  (hQ i j).not_gt ((cond_lt_iff_hContrary ctx hm hcip hi hj).mpr (.inl ⟨h.1, h.2.1⟩))

-- Corollary 11, Theorem 9
theorem not_butFelicitous_defaultButCtx {E : Type*} (μ : Measure W) [IsProbabilityMeasure μ]
    {Q : E → Set W} (hQ : NonnegInstantialRelevance μ Q) {i j : E} (hmi : MeasurableSet (Q i))
    (hmj : MeasurableSet (Q j)) (hi : μ (Q i) ≠ 0) (hj : μ (Q j) ≠ 0) (hjc : μ (Q j)ᶜ ≠ 0) :
    ¬ ButFelicitous (defaultButCtx μ (Q j) hmj) (Q i) (Q j) :=
  have : (defaultButCtx μ (Q j) hmj).Nondegenerate := ⟨hjc, by rwa [compl_compl]⟩
  not_butFelicitous_of_nonnegInstantialRelevance _ hQ hmi
    (condIndepIssue_defaultButCtx μ hmi hmj) hi hj

/-! ### *Also* -/

/-- Definition 12: A is presupposed when conditioning on A changes no probability. -/
def IsPresupposed (μ : Measure W) (a : Set W) : Prop :=
  μ[|a] = μ

theorem isPresupposed_iff {μ : Measure W} [IsProbabilityMeasure μ] {a : Set W}
    (ha : MeasurableSet a) : IsPresupposed μ a ↔ μ a = 1 := by
  constructor
  · intro h
    have h0 : μ a ≠ 0 := fun h0 ↦ by
      have := congrArg (· Set.univ) h
      simp [cond_eq_zero_of_meas_eq_zero h0] at this
    calc μ a = μ[|a] a := by rw [h]
      _ = 1 := cond_apply_self h0 (measure_ne_top _ _)
  · intro h1
    rw [IsPresupposed, ProbabilityTheory.cond, h1, inv_one, one_smul,
      Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr ((prob_compl_eq_zero_iff ha).mpr h1))]

variable {ctx : Context W} {a : Set W}

-- Fact 17
theorem IsPresupposed.bayesFactor_inter [IsProbabilityMeasure ctx.prior]
    (h : IsPresupposed ctx.prior a) (ha : MeasurableSet a) (b : Set W) :
    bayesFactor ctx (a ∩ b) = bayesFactor ctx b := by
  have hc := (prob_compl_eq_zero_iff ha).mpr ((isPresupposed_iff ha).mp h)
  rw [bayesFactor_def, bayesFactor_def, Set.inter_comm,
    measure_inter_conull (cond_absolutelyContinuous hc),
    measure_inter_conull (cond_absolutelyContinuous hc)]

theorem IsPresupposed.irrelevant [IsProbabilityMeasure ctx.prior] [ctx.Nondegenerate]
    (h : IsPresupposed ctx.prior a) (ha : MeasurableSet a) : irrelevant ctx a := by
  have hc := (prob_compl_eq_zero_iff ha).mpr ((isPresupposed_iff ha).mp h)
  have hm := ctx.topicMeasurable
  rw [DTS.irrelevant, bayesFactor_def, cond_apply hm, cond_apply hm.compl, measure_inter_conull hc,
    measure_inter_conull hc,
    ENNReal.inv_mul_cancel Context.Nondegenerate.topic_ne_zero (measure_ne_top _ _),
    ENNReal.inv_mul_cancel Context.Nondegenerate.compl_ne_zero (measure_ne_top _ _), div_one]

-- Fact 17
theorem IsPresupposed.bayesFactor_inter_eq_mul [IsProbabilityMeasure ctx.prior]
    [ctx.Nondegenerate] (h : IsPresupposed ctx.prior a) (ha : MeasurableSet a) (b : Set W) :
    bayesFactor ctx (a ∩ b) = bayesFactor ctx a * bayesFactor ctx b := by
  rw [h.bayesFactor_inter ha, h.irrelevant ha, one_mul]

/-- Definition 13: D is topic-anaphorically salient for E in context `ctx` when E is relevant to
the issue, D is presupposed, and in an earlier context `ctx₀` on the same issue, where D was not
yet presupposed, D was relevant. -/
structure TopicAnaphoricallySalient (ctx₀ ctx : Context W) (d e : Set W) : Prop where
  topic_eq : ctx₀.topic = ctx.topic
  relevant : ¬ irrelevant ctx e
  presupposed : IsPresupposed ctx.prior d
  lt_one : ctx₀.prior d < 1
  wasRelevant : ¬ irrelevant ctx₀ d

/-- Hypothesis 8, *(and) also*: also(b, B) is felicitous only if Ba is topic-anaphorically
salient for Bb and Ba had, when it was relevant, the relevance sign Bb has now. -/
def AlsoFelicitous (ctx₀ ctx : Context W) (ba bb : Set W) : Prop :=
  TopicAnaphoricallySalient ctx₀ ctx ba bb ∧
    compare (bayesFactor ctx₀ ba) 1 = compare (bayesFactor ctx bb) 1

/-- Hypothesis 8, *but also*: the signs are opposite. -/
def ButAlsoFelicitous (ctx₀ ctx : Context W) (ba bb : Set W) : Prop :=
  TopicAnaphoricallySalient ctx₀ ctx ba bb ∧
    compare (bayesFactor ctx₀ ba) 1 = (compare (bayesFactor ctx bb) 1).swap

-- Corollary 15
theorem TopicAnaphoricallySalient.ne {E : Type*} {ctx₀ : Context W}
    [IsProbabilityMeasure ctx.prior] [ctx.Nondegenerate] {B : E → Set W} {i j : E}
    (h : TopicAnaphoricallySalient ctx₀ ctx (B i) (B j)) (hm : MeasurableSet (B i)) : i ≠ j := by
  rintro rfl
  exact h.relevant (h.presupposed.irrelevant hm)

/-- Partial Definition 14: φ is properly accommodable only if it is contingent and irrelevant to
the issue. -/
def ProperlyAccommodable (ctx : Context W) (φ : Set W) : Prop :=
  0 < ctx.prior φ ∧ ctx.prior φ < 1 ∧ irrelevant ctx φ

theorem TopicAnaphoricallySalient.not_properlyAccommodable {ctx₀ : Context W} {d e : Set W}
    (h : TopicAnaphoricallySalient ctx₀ ctx d e) : ¬ ProperlyAccommodable ctx₀ d :=
  fun hacc ↦ h.wasRelevant hacc.2.2

/-- Partial Definition 15: A has prima facie causal responsibility for B only if A makes B more
probable. -/
def PrimaFacieCause (μ : Measure W) (a b : Set W) : Prop :=
  μ b < μ[|a] b

-- Corollary 16
theorem IsPresupposed.not_primaFacieCause {μ : Measure W} (h : IsPresupposed μ a)
    (b : Set W) : ¬ PrimaFacieCause μ a b := by
  rw [PrimaFacieCause, h]
  exact lt_irrefl _

theorem AlsoFelicitous.not_primaFacieCause {ctx₀ : Context W} {ba bb : Set W}
    (h : AlsoFelicitous ctx₀ ctx ba bb) : ¬ PrimaFacieCause ctx.prior ba bb :=
  h.1.presupposed.not_primaFacieCause bb

end Merin1999a
