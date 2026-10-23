module

public import Linglib.Pragmatics.RSA.QUD
public import Linglib.Semantics.Aspect.Phasal

/-!
# Qing, Goodman, and Lassiter (2016): A Rational Speech-Act Model of Projective Content

Qing, Goodman and Lassiter derive the projective content of change-of-state verbs under negation
from a listener who jointly infers the world and the context set the speaker took for granted.
The worlds record whether John smoked and whether he smokes. Within a context set the literal
listener answers the question under discussion (`L0`), the speaker is informative about the
answer (`speaker`), and the pragmatic listener inverts the speaker over pairs of a world and a
context set (`listener`).

## Main results

* `standard_uniform`: the standard model puts the three worlds compatible with *John did not stop
  smoking* on a par at every rationality.
* `uniform_tie`, `uniform_change_lt`: with every context set equally likely and the maximal
  question, the world in which John still smokes, with the context set that he smoked, ties with
  the world in which he never smoked, with the context set that he does not smoke, and the
  changed world trails.
* `now_settled_lt`, `now_change_lt`, `now_universe_lt`: asked whether John smokes now, the
  listener prefers the world in which he still smokes with the context set that he smoked to a
  context set that already settles the question, to the *change* context set, and, at every
  rationality of at least one, to the universe.
* `now_cg_mode`: the paper's common-ground prior is one instance.

## Implementation notes

* The utterance prior enters the speaker as the cost `-log Pr(u) / α`, since the paper multiplies
  by the prior outside the rationality.
* The pair prior puts the actual world in the context set, as the paper's figures do.
* Speaker shares are evaluated cell by cell from tables of the literal listener's counts,
  certified by `decide`.
* The common-ground prior carries the paper's observation probability of `0.4` and `5%` noise,
  scaled to naturals. The theorems quantify over any prior meeting the ordering hypotheses it
  satisfies.

## TODO

* The world marginals of the paper's first figure and the questions of its fourth are not
  formalized.

## References

* [qing-goodman-lassiter-2016]
* [frank-goodman-2012]
* [stalnaker-1974]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace QingGoodmanLassiter2016

/-! ### Worlds, utterances, and questions -/

/-- A world records whether John smoked in the past and whether he smokes now. -/
inductive World
  | TT | TF | FT | FF
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace World := ⊤
instance : DiscreteMeasurableSpace World := ⟨fun _ ↦ trivial⟩
instance : MeasurableSingletonClass World := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- John smoked in the past. -/
def World.past : World → Bool
  | .TT | .TF => true
  | .FT | .FF => false

/-- John smokes now. -/
def World.now : World → Bool
  | .TT | .FT => true
  | .TF | .FF => false

/-- The six positive utterances of Table 1. -/
inductive Positive
  | smokes | smoked | always | stopped | started | never
  deriving DecidableEq, Fintype, Repr, Inhabited

open Aspect in
/-- The denotation of a positive utterance, the change-of-state verbs evaluated at the world's
two times. -/
def Positive.ext : Positive → Set World
  | .smokes => {w | w.now}
  | .smoked => {w | w.past}
  | .always => {w | Phasal.continuation.Transition w.past w.now}
  | .stopped => {w | Phasal.cessation.Transition w.past w.now}
  | .started => {w | Phasal.inception.Transition w.past w.now}
  | .never => {w | ¬ w.past ∧ ¬ w.now}

instance : ∀ p : Positive, DecidablePred (· ∈ p.ext)
  | .smokes, _ => inferInstanceAs (Decidable (_ = true))
  | .smoked, _ => inferInstanceAs (Decidable (_ = true))
  | .always, _ => inferInstanceAs (Decidable (Aspect.Phasal.Transition _ _ _))
  | .stopped, _ => inferInstanceAs (Decidable (Aspect.Phasal.Transition _ _ _))
  | .started, _ => inferInstanceAs (Decidable (Aspect.Phasal.Transition _ _ _))
  | .never, _ => inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

/-- An utterance is silence or a positive utterance, affirmed or negated. -/
inductive Utterance
  | silence
  | say (p : Positive) (negated : Bool)
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ ↦ trivial⟩
instance : MeasurableSingletonClass Utterance :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- Silence is true everywhere, and a negation denotes the complement. -/
def Utterance.sem : Utterance → Set World
  | .silence => Set.univ
  | .say p false => p.ext
  | .say p true => p.extᶜ

instance : ∀ u : Utterance, DecidablePred (· ∈ u.sem)
  | .silence, _ => inferInstanceAs (Decidable True)
  | .say p false, w => inferInstanceAs (Decidable (w ∈ p.ext))
  | .say p true, w => inferInstanceAs (Decidable (¬ w ∈ p.ext))

/-- *John did not stop smoking*. -/
abbrev notStopped : Utterance := .say .stopped true

/-- The utterance prior (1) halves with each content word, negation and auxiliaries being
free. -/
noncomputable def Utterance.prior : Utterance → ℝ≥0∞
  | .silence => 1
  | .say .smokes _ | .say .smoked _ => 1 / 2
  | .say _ _ => 1 / 4

/-- The question under discussion asks which world it is, or whether John smokes now. -/
inductive QUD
  | max | now
  deriving DecidableEq, Repr

/-- The cell of a world under a question. -/
def QUD.cell : QUD → World → Finset World
  | .max, w => {w}
  | .now, w => Finset.univ.filter (·.now = w.now)

theorem QUD.cell_preimage (q : QUD) (w : World) : q.cell ⁻¹' {q.cell w} = ↑(q.cell w) := by
  ext w'
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe]
  cases q <;> cases w <;> cases w' <;> decide

/-! ### Context sets -/

/-- The context set that John smoked. -/
def pastT : Finset World := {.TT, .TF}
/-- The context set that John does not smoke. -/
def nowF : Finset World := {.TF, .FF}
/-- The context set that John smokes. -/
def nowT : Finset World := {.TT, .FT}
/-- The context set that John's habit changed, one way or the other. -/
def change : Finset World := {.TF, .FT}

/-! ### The literal listener within a context set (5) -/

/-- The literal listener within a context set under a question samples a world of the context
set at which the utterance is true and returns the question's answer there. -/
noncomputable def L0 (C : Finset World) (q : QUD) : Kernel Utterance (Finset World) :=
  (RSA.listener (Measure.count.restrict ↑C) (truthful fun u ↦ u.sem)).map q.cell

instance (C : Finset World) (q : QUD) : IsFiniteKernel (L0 C q) :=
  inferInstanceAs (IsFiniteKernel (Kernel.map _ _))

/-- The literal listener counts the worlds of the context set where the utterance is true and
the question's answer is the world's, over those where the utterance is true. -/
def l0 (C : Finset World) (q : QUD) (u : Utterance) (w : World) : ℕ × ℕ :=
  (((C.filter (· ∈ u.sem)).filter (· ∈ q.cell w)).card, (C.filter (· ∈ u.sem)).card)

theorem L0_apply (C : Finset World) (q : QUD) (u : Utterance) (w : World) :
    L0 C q u {q.cell w} = ((l0 C q u w).1 : ℝ≥0∞) / (l0 C q u w).2 := by
  have e1 : u.sem ∩ ↑C = ↑(C.filter (· ∈ u.sem)) := by ext; simp [and_comm]
  have e2 : u.sem ∩ ↑(q.cell w) ∩ ↑C = ↑((C.filter (· ∈ u.sem)).filter (· ∈ q.cell w)) := by
    ext; simp; tauto
  rw [L0, listener_truthful_map_apply_singleton, QUD.cell_preimage,
    Measure.restrict_apply .of_discrete, Measure.restrict_apply .of_discrete, e1, e2,
    Measure.count_apply_finset, Measure.count_apply_finset, l0]

theorem prior_ne_zero (u : Utterance) : u.prior ≠ 0 := by
  rcases u with _ | ⟨p, b⟩ <;> try cases p
  all_goals simp [Utterance.prior]

theorem prior_ne_top (u : Utterance) : u.prior ≠ ∞ := by
  rcases u with _ | ⟨p, b⟩ <;> try cases p
  all_goals simp [Utterance.prior]

/-- An utterance costs `-log Pr(u) / α` at rationality `α`, since (3) weighs the speaker's
choice by the utterance prior outside the rationality. -/
noncomputable def cost (α : ℝ) (u : Utterance) : ℝ := -Real.log u.prior.toReal / α

theorem exp_neg_cost {α : ℝ} (hα : α ≠ 0) (u : Utterance) :
    Real.exp (-(α * cost α u)) = u.prior.toReal := by
  rw [cost, mul_div_cancel₀ _ hα, neg_neg,
    Real.exp_log (ENNReal.toReal_pos (prior_ne_zero u) (prior_ne_top u))]

/-! ### Speaker and listeners (6), (7) -/

/-- The speaker within a context set (6) knows the answer to the question at her world and is
informative about the literal listener's belief about it, weighted by the utterance prior. -/
noncomputable def speaker (q : QUD) (C : Finset World) (α : ℝ) (w : World) : Measure Utterance :=
  RSA.speaker α (cost α) (L0 C q) Measure.dirac (q.cell w)

instance (q : QUD) (C : Finset World) (α : ℝ) (w : World) : IsFiniteMeasure (speaker q C α w) :=
  inferInstanceAs (IsFiniteMeasure (RSA.speaker _ _ _ _ _))

/-- The prior over context sets determined by a weighting. -/
noncomputable def ctxPrior (π : Finset World → ℕ) : Measure (Finset World) :=
  Measure.count.withDensity fun C ↦ (π C : ℝ≥0∞)

theorem ctxPrior_singleton (π : Finset World → ℕ) (C : Finset World) :
    ctxPrior π {C} = π C := by
  rw [ctxPrior, withDensity_apply _ (measurableSet_singleton C), lintegral_singleton,
    Measure.count_singleton, mul_one]

instance (π : Finset World → ℕ) : IsFiniteMeasure (ctxPrior π) :=
  ⟨by
    rw [ctxPrior, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count,
      tsum_fintype]
    exact ENNReal.sum_lt_top.mpr fun C _ ↦ ENNReal.natCast_lt_top _⟩

/-- The pair prior weighs a world with a context set containing it by the context prior; the
paper's uniform world prior cancels. -/
noncomputable def pairPrior (π : Finset World → ℕ) : Measure (World × Finset World) :=
  (Measure.count.prod (ctxPrior π)).restrict {p | p.1 ∈ p.2}

@[simp] theorem pairPrior_singleton (π : Finset World → ℕ) (w : World) (C : Finset World) :
    pairPrior π {(w, C)} = if w ∈ C then (π C : ℝ≥0∞) else 0 := by
  rw [pairPrior, Measure.restrict_apply (measurableSet_singleton _)]
  split_ifs with h
  · rw [Set.inter_eq_self_of_subset_left (s := ({(w, C)} : Set (World × Finset World)))
        (Set.singleton_subset_iff.mpr h),
      ← Set.singleton_prod_singleton, Measure.prod_prod, Measure.count_singleton,
      ctxPrior_singleton, one_mul]
  · rw [(Set.singleton_inter_eq_empty (a := (w, C))
        (s := {p : World × Finset World | p.1 ∈ p.2})).mpr h, measure_empty]

instance (π : Finset World → ℕ) : IsFiniteMeasure (pairPrior π) :=
  inferInstanceAs (IsFiniteMeasure ((Measure.count.prod (ctxPrior π)).restrict _))

/-- The joint listener (7) inverts the speaker within each context set against the pair prior. -/
noncomputable def listener (q : QUD) (π : Finset World → ℕ) (α : ℝ) :
    Kernel Utterance (World × Finset World) :=
  RSA.listener (pairPrior π) fun p ↦ speaker q p.2 α p.1

/-- The common-ground prior (8) takes the paper's observation probability `0.4` and `5%`
noise, scaled by `14700`, over the universe, the four single observations, the four pairs, and
the six context sets no observations derive. -/
def cgWeight (C : Finset World) : ℕ :=
  if C.card = 4 then 2614
  else if C = pastT ∨ C = nowT ∨ C = nowF ∨ C = {.FT, .FF} then 1759
  else if C.card = 1 then 1189 else 49

/-! ### Evaluating a cell -/

private theorem sum_utterance {M : Type*} [AddCommMonoid M] (f : Utterance → M) :
    ∑ u, f u = f .silence + f (.say .smokes false) + f (.say .smokes true)
      + f (.say .smoked false) + f (.say .smoked true) + f (.say .always false)
      + f (.say .always true) + f (.say .stopped false) + f (.say .stopped true)
      + f (.say .started false) + f (.say .started true) + f (.say .never false)
      + f (.say .never true) := by
  rw [show (Finset.univ : Finset Utterance) = {.silence, .say .smokes false, .say .smokes true,
      .say .smoked false, .say .smoked true, .say .always false, .say .always true,
      .say .stopped false, .say .stopped true, .say .started false, .say .started true,
      .say .never false, .say .never true} by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [add_assoc]

/-- The share of *did not stop smoking* at a cell, on reals. -/
noncomputable def share (q : QUD) (C : Finset World) (w : World) (α : ℝ) : ℝ :=
  (speaker q C α w).real {notStopped}

private theorem share_eq (q : QUD) (C : Finset World) (w : World) {α : ℝ} (hα : 0 < α) :
    share q C w α =
      ((L0 C q notStopped {q.cell w} ^ α).toReal * (notStopped.prior).toReal
        / ∑ u, (L0 C q u {q.cell w} ^ α).toReal * u.prior.toReal) := by
  rw [share, speaker, speaker_dirac_real_singleton hα.le]
  simp only [exp_neg_cost hα.ne']

/-- The literal listener's cells at `pastT`, `now`, `TT`. -/
private def tblA : Utterance → ℕ × ℕ
  | .silence => (1, 2)
  | .say .smokes false => (1, 1)
  | .say .smokes true => (0, 1)
  | .say .smoked false => (1, 2)
  | .say .smoked true => (0, 0)
  | .say .always false => (1, 1)
  | .say .always true => (0, 1)
  | .say .stopped false => (0, 1)
  | .say .stopped true => (1, 1)
  | .say .started false => (0, 0)
  | .say .started true => (1, 2)
  | .say .never false => (0, 0)
  | .say .never true => (1, 2)

private theorem l0_A : ∀ u, l0 pastT .now u .TT = tblA u := by decide

/-- The literal listener's cells at `nowF`, `now`, `FF`. -/
private def tblB : Utterance → ℕ × ℕ
  | .silence => (2, 2)
  | .say .smokes false => (0, 0)
  | .say .smokes true => (2, 2)
  | .say .smoked false => (1, 1)
  | .say .smoked true => (1, 1)
  | .say .always false => (0, 0)
  | .say .always true => (2, 2)
  | .say .stopped false => (1, 1)
  | .say .stopped true => (1, 1)
  | .say .started false => (0, 0)
  | .say .started true => (2, 2)
  | .say .never false => (1, 1)
  | .say .never true => (1, 1)

private theorem l0_B : ∀ u, l0 nowF .now u .FF = tblB u := by decide

/-- The literal listener's cells at `change`, `now`, `FT`. -/
private def tblC : Utterance → ℕ × ℕ
  | .silence => (1, 2)
  | .say .smokes false => (1, 1)
  | .say .smokes true => (0, 1)
  | .say .smoked false => (0, 1)
  | .say .smoked true => (1, 1)
  | .say .always false => (0, 0)
  | .say .always true => (1, 2)
  | .say .stopped false => (0, 1)
  | .say .stopped true => (1, 1)
  | .say .started false => (1, 1)
  | .say .started true => (0, 1)
  | .say .never false => (0, 0)
  | .say .never true => (1, 2)

private theorem l0_C : ∀ u, l0 change .now u .FT = tblC u := by decide

/-- The literal listener's cells at `Finset.univ`, `now`, `TT`. -/
private def tblD : Utterance → ℕ × ℕ
  | .silence => (2, 4)
  | .say .smokes false => (2, 2)
  | .say .smokes true => (0, 2)
  | .say .smoked false => (1, 2)
  | .say .smoked true => (1, 2)
  | .say .always false => (1, 1)
  | .say .always true => (1, 3)
  | .say .stopped false => (0, 1)
  | .say .stopped true => (2, 3)
  | .say .started false => (1, 1)
  | .say .started true => (1, 3)
  | .say .never false => (0, 1)
  | .say .never true => (2, 3)

private theorem l0_D : ∀ u, l0 Finset.univ .now u .TT = tblD u := by decide

/-- The literal listener's cells at `nowT`, `now`, `TT`. -/
private def tblE : Utterance → ℕ × ℕ
  | .silence => (2, 2)
  | .say .smokes false => (2, 2)
  | .say .smokes true => (0, 0)
  | .say .smoked false => (1, 1)
  | .say .smoked true => (1, 1)
  | .say .always false => (1, 1)
  | .say .always true => (1, 1)
  | .say .stopped false => (0, 0)
  | .say .stopped true => (2, 2)
  | .say .started false => (1, 1)
  | .say .started true => (1, 1)
  | .say .never false => (0, 0)
  | .say .never true => (2, 2)

private theorem l0_E : ∀ u, l0 nowT .now u .TT = tblE u := by decide

/-- The literal listener's cells at `pastT`, `max`, `TT`. -/
private def tblF : Utterance → ℕ × ℕ
  | .silence => (1, 2)
  | .say .smokes false => (1, 1)
  | .say .smokes true => (0, 1)
  | .say .smoked false => (1, 2)
  | .say .smoked true => (0, 0)
  | .say .always false => (1, 1)
  | .say .always true => (0, 1)
  | .say .stopped false => (0, 1)
  | .say .stopped true => (1, 1)
  | .say .started false => (0, 0)
  | .say .started true => (1, 2)
  | .say .never false => (0, 0)
  | .say .never true => (1, 2)

private theorem l0_F : ∀ u, l0 pastT .max u .TT = tblF u := by decide

/-- The literal listener's cells at `nowF`, `max`, `FF`. -/
private def tblG : Utterance → ℕ × ℕ
  | .silence => (1, 2)
  | .say .smokes false => (0, 0)
  | .say .smokes true => (1, 2)
  | .say .smoked false => (0, 1)
  | .say .smoked true => (1, 1)
  | .say .always false => (0, 0)
  | .say .always true => (1, 2)
  | .say .stopped false => (0, 1)
  | .say .stopped true => (1, 1)
  | .say .started false => (0, 0)
  | .say .started true => (1, 2)
  | .say .never false => (1, 1)
  | .say .never true => (0, 1)

private theorem l0_G : ∀ u, l0 nowF .max u .FF = tblG u := by decide

/-- The literal listener's cells at `change`, `max`, `FT`. -/
private def tblH : Utterance → ℕ × ℕ
  | .silence => (1, 2)
  | .say .smokes false => (1, 1)
  | .say .smokes true => (0, 1)
  | .say .smoked false => (0, 1)
  | .say .smoked true => (1, 1)
  | .say .always false => (0, 0)
  | .say .always true => (1, 2)
  | .say .stopped false => (0, 1)
  | .say .stopped true => (1, 1)
  | .say .started false => (1, 1)
  | .say .started true => (0, 1)
  | .say .never false => (0, 0)
  | .say .never true => (1, 2)

private theorem l0_H : ∀ u, l0 change .max u .FT = tblH u := by decide

/-- The literal listener's cells at `Finset.univ`, `max`, `TT`. -/
private def tblI : Utterance → ℕ × ℕ
  | .silence => (1, 4)
  | .say .smokes false => (1, 2)
  | .say .smokes true => (0, 2)
  | .say .smoked false => (1, 2)
  | .say .smoked true => (0, 2)
  | .say .always false => (1, 1)
  | .say .always true => (0, 3)
  | .say .stopped false => (0, 1)
  | .say .stopped true => (1, 3)
  | .say .started false => (0, 1)
  | .say .started true => (1, 3)
  | .say .never false => (0, 1)
  | .say .never true => (1, 3)

private theorem l0_I : ∀ u, l0 Finset.univ .max u .TT = tblI u := by decide

/-- The literal listener's cells at `Finset.univ`, `max`, `FT`. -/
private def tblJ : Utterance → ℕ × ℕ
  | .silence => (1, 4)
  | .say .smokes false => (1, 2)
  | .say .smokes true => (0, 2)
  | .say .smoked false => (0, 2)
  | .say .smoked true => (1, 2)
  | .say .always false => (0, 1)
  | .say .always true => (1, 3)
  | .say .stopped false => (0, 1)
  | .say .stopped true => (1, 3)
  | .say .started false => (1, 1)
  | .say .started true => (0, 3)
  | .say .never false => (0, 1)
  | .say .never true => (1, 3)

private theorem l0_J : ∀ u, l0 Finset.univ .max u .FT = tblJ u := by decide

/-- The literal listener's cells at `Finset.univ`, `max`, `FF`. -/
private def tblK : Utterance → ℕ × ℕ
  | .silence => (1, 4)
  | .say .smokes false => (0, 2)
  | .say .smokes true => (1, 2)
  | .say .smoked false => (0, 2)
  | .say .smoked true => (1, 2)
  | .say .always false => (0, 1)
  | .say .always true => (1, 3)
  | .say .stopped false => (0, 1)
  | .say .stopped true => (1, 3)
  | .say .started false => (0, 1)
  | .say .started true => (1, 3)
  | .say .never false => (1, 1)
  | .say .never true => (0, 3)

private theorem l0_K : ∀ u, l0 Finset.univ .max u .FF = tblK u := by decide


private theorem toReal_frac_rpow (n m : ℕ) (α : ℝ) :
    (((n : ℝ≥0∞) / m) ^ α).toReal = ((n : ℝ) / m) ^ α := by
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

private theorem prior_toReal :
    (Utterance.silence.prior).toReal = 1 ∧
    (∀ b, (Utterance.say .smokes b).prior.toReal = 1 / 2) ∧
    (∀ b, (Utterance.say .smoked b).prior.toReal = 1 / 2) ∧
    (∀ b, (Utterance.say .always b).prior.toReal = 1 / 4) ∧
    (∀ b, (Utterance.say .stopped b).prior.toReal = 1 / 4) ∧
    (∀ b, (Utterance.say .started b).prior.toReal = 1 / 4) ∧
    (∀ b, (Utterance.say .never b).prior.toReal = 1 / 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp [Utterance.prior]

private theorem share_expand (q : QUD) (C : Finset World) (w : World) {α : ℝ} (hα : 0 < α)
    (tbl : Utterance → ℕ × ℕ) (htbl : ∀ u, l0 C q u w = tbl u) :
    share q C w α =
      (((tbl notStopped).1 : ℝ) / (tbl notStopped).2) ^ α * (1 / 4) /
        (((tbl .silence).1 / (tbl .silence).2) ^ α * 1
          + ((tbl (.say .smokes false)).1 / (tbl (.say .smokes false)).2) ^ α * (1 / 2)
          + ((tbl (.say .smokes true)).1 / (tbl (.say .smokes true)).2) ^ α * (1 / 2)
          + ((tbl (.say .smoked false)).1 / (tbl (.say .smoked false)).2) ^ α * (1 / 2)
          + ((tbl (.say .smoked true)).1 / (tbl (.say .smoked true)).2) ^ α * (1 / 2)
          + ((tbl (.say .always false)).1 / (tbl (.say .always false)).2) ^ α * (1 / 4)
          + ((tbl (.say .always true)).1 / (tbl (.say .always true)).2) ^ α * (1 / 4)
          + ((tbl (.say .stopped false)).1 / (tbl (.say .stopped false)).2) ^ α * (1 / 4)
          + ((tbl (.say .stopped true)).1 / (tbl (.say .stopped true)).2) ^ α * (1 / 4)
          + ((tbl (.say .started false)).1 / (tbl (.say .started false)).2) ^ α * (1 / 4)
          + ((tbl (.say .started true)).1 / (tbl (.say .started true)).2) ^ α * (1 / 4)
          + ((tbl (.say .never false)).1 / (tbl (.say .never false)).2) ^ α * (1 / 4)
          + ((tbl (.say .never true)).1 / (tbl (.say .never true)).2) ^ α * (1 / 4)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := prior_toReal
  rw [share_eq _ _ _ hα, sum_utterance]
  simp only [L0_apply, htbl, toReal_frac_rpow, h0, h1, h2, h3, h4, h5, h6]

section Cells

variable {α : ℝ} (hα : 0 < α)
include hα

private theorem share_A : share .now pastT .TT α = 1 / (4 * (1 + 2 * (1 / 2 : ℝ) ^ α)) := by
  rw [share_expand _ _ _ hα tblA l0_A]
  dsimp only [tblA]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  norm_num [Real.zero_rpow hα.ne']
  ring

private theorem share_B : share .now nowF .FF α = 1 / 16 := by
  rw [share_expand _ _ _ hα tblB l0_B]
  dsimp only [tblB]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  norm_num [Real.zero_rpow hα.ne']

private theorem share_C : share .now change .FT α = 1 / (6 * (1 + (1 / 2 : ℝ) ^ α)) := by
  rw [share_expand _ _ _ hα tblC l0_C]
  dsimp only [tblC]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  norm_num [Real.zero_rpow hα.ne']
  ring

private theorem share_D :
    share .now Finset.univ .TT α =
      (2 / 3 : ℝ) ^ α /
        (4 + 8 * (1 / 2 : ℝ) ^ α + 2 * (2 / 3 : ℝ) ^ α + 2 * (1 / 3 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblD l0_D]
  dsimp only [tblD]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  norm_num [Real.zero_rpow hα.ne']
  ring

private theorem share_E : share .now nowT .TT α = 1 / 16 := by
  rw [share_expand _ _ _ hα tblE l0_E]
  dsimp only [tblE]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  norm_num [Real.zero_rpow hα.ne']

private theorem share_F : share .max pastT .TT α = 1 / (4 * (1 + 2 * (1 / 2 : ℝ) ^ α)) := by
  rw [share_expand _ _ _ hα tblF l0_F]
  dsimp only [tblF]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  norm_num [Real.zero_rpow hα.ne']
  ring

private theorem share_G : share .max nowF .FF α = 1 / (4 * (1 + 2 * (1 / 2 : ℝ) ^ α)) := by
  rw [share_expand _ _ _ hα tblG l0_G]
  dsimp only [tblG]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  norm_num [Real.zero_rpow hα.ne']
  ring

private theorem share_H : share .max change .FT α = 1 / (6 * (1 + (1 / 2 : ℝ) ^ α)) := by
  rw [share_expand _ _ _ hα tblH l0_H]
  dsimp only [tblH]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  norm_num [Real.zero_rpow hα.ne']
  ring

private theorem share_IJK :
    share .max Finset.univ .TT α = share .max Finset.univ .FT α ∧
      share .max Finset.univ .FT α = share .max Finset.univ .FF α := by
  rw [share_expand _ _ _ hα tblI l0_I, share_expand _ _ _ hα tblJ l0_J,
    share_expand _ _ _ hα tblK l0_K]
  dsimp only [tblI, tblJ, tblK]
  norm_num [Real.zero_rpow hα.ne']
  constructor <;> ring

end Cells

/-! ### Listener comparisons -/

private theorem pairPrior_real (π : Finset World → ℕ) (w : World) (C : Finset World)
    (h : w ∈ C) : (pairPrior π).real {(w, C)} = π C := by
  rw [measureReal_def, pairPrior_singleton, ite_eq_left h, ENNReal.toReal_natCast]

/-- Listener preference between two pairs is prior-weighted share preference. -/
private theorem listener_lt_iff (q : QUD) (π : Finset World → ℕ) {α : ℝ} (w₁ w₂ : World)
    (C₁ C₂ : Finset World) (h₁ : w₁ ∈ C₁) (h₂ : w₂ ∈ C₂) :
    (listener q π α notStopped).real {(w₁, C₁)} < (listener q π α notStopped).real {(w₂, C₂)}
      ↔ (π C₁ : ℝ) * share q C₁ w₁ α < π C₂ * share q C₂ w₂ α := by
  rw [listener, RSA.listener_real_singleton_lt_iff, pairPrior_real π _ _ h₁,
    pairPrior_real π _ _ h₂]
  rfl

private theorem listener_eq (q : QUD) (π : Finset World → ℕ) {α : ℝ} (w₁ w₂ : World)
    (C₁ C₂ : Finset World)
    (hprior : pairPrior π {(w₁, C₁)} = pairPrior π {(w₂, C₂)})
    (hshare : speaker q C₁ α w₁ {notStopped} = speaker q C₂ α w₂ {notStopped}) :
    listener q π α notStopped {(w₁, C₁)} = listener q π α notStopped {(w₂, C₂)} := by
  rw [listener]
  exact RSA.listener_apply_singleton_congr _ _ hshare hprior


/-! ### The standard model (Figure 1a) -/

/-- The standard listener is the pragmatic listener over the universe with a uniform world
prior, the first column of Table 2. -/
noncomputable def standard (α : ℝ) : Kernel Utterance World :=
  RSA.listener (uniformOn Set.univ) (speaker .max Finset.univ α)

/-- The standard model puts the three worlds compatible with *did not stop smoking* on a par at
every rationality, since the utterance is equally under-informative at each, so nothing
projects. -/
theorem standard_uniform {α : ℝ} (hα : 0 < α) :
    standard α notStopped {.TT} = standard α notStopped {.FT} ∧
      standard α notStopped {.FT} = standard α notStopped {.FF} := by
  obtain ⟨h₁, h₂⟩ := share_IJK hα
  refine ⟨?_, ?_⟩
  · rw [standard]
    exact RSA.listener_apply_singleton_congr _ _
      ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h₁)
      (uniformOn_univ_singleton_eq _ _)
  · rw [standard]
    exact RSA.listener_apply_singleton_congr _ _
      ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h₂)
      (uniformOn_univ_singleton_eq _ _)

/-! ### Context sets under the maximal question (Figures 1b, 2a) -/

/-- With every context set equally likely, the world in which John still smokes taken with the
context set that he smoked ties with the world in which he never smoked taken with the context
set that he does not smoke, since *did not stop smoking* identifies the world within either. -/
theorem uniform_tie {α : ℝ} (hα : 0 < α) :
    listener .max (fun _ ↦ 1) α notStopped {(.TT, pastT)}
      = listener .max (fun _ ↦ 1) α notStopped {(.FF, nowF)} :=
  listener_eq .max _ _ _ _ _
    (by rw [pairPrior_singleton, pairPrior_singleton, ite_eq_left (by decide),
      ite_eq_left (by decide)])
    ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
      ((share_F hα).trans (share_G hα).symm))

private theorem half_rpow_lt_one {α : ℝ} (hα : 0 < α) : (1 / 2 : ℝ) ^ α < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) hα

/-- The changed world with the *change* context set trails, since *did not stop smoking*
identifies it there too, but against more informative competitors. -/
theorem uniform_change_lt {α : ℝ} (hα : 0 < α) :
    (listener .max (fun _ ↦ 1) α notStopped).real {(.FT, change)}
      < (listener .max (fun _ ↦ 1) α notStopped).real {(.TT, pastT)} := by
  rw [listener_lt_iff .max _ _ _ _ _ (by decide) (by decide), share_H hα,
    share_F hα]
  have hx := half_rpow_lt_one hα
  have hx0 : (0 : ℝ) < (1 / 2 : ℝ) ^ α := by positivity
  simp only [Nat.cast_one, one_mul]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### The question whether John smokes now (Figures 1d, 3) -/

/-- A context set that already settles the question, that he does not smoke or that he does,
has made silence maximally informative and cannot explain the utterance. Either loses to the
world in which he still smokes with the context set that he smoked, under any prior weighting
that context set at least as much. -/
theorem now_settled_lt (π : Finset World → ℕ) (hπ : π pastT ≠ 0) (hF : π nowF ≤ π pastT)
    (hT : π nowT ≤ π pastT) {α : ℝ} (hα : 0 < α) :
    (listener .now π α notStopped).real {(.FF, nowF)}
        < (listener .now π α notStopped).real {(.TT, pastT)} ∧
      (listener .now π α notStopped).real {(.TT, nowT)}
        < (listener .now π α notStopped).real {(.TT, pastT)} := by
  have hx := half_rpow_lt_one hα
  have hx0 : (0 : ℝ) < (1 / 2 : ℝ) ^ α := by positivity
  have hπ' : (0 : ℝ) < π pastT := by exact_mod_cast Nat.pos_of_ne_zero hπ
  have hF' : (π nowF : ℝ) ≤ π pastT := by exact_mod_cast hF
  have hT' : (π nowT : ℝ) ≤ π pastT := by exact_mod_cast hT
  constructor
  · rw [listener_lt_iff .now π _ _ _ _ (by decide) (by decide), share_B hα, share_A hα,
      mul_one_div, mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [listener_lt_iff .now π _ _ _ _ (by decide) (by decide), share_E hα, share_A hα,
      mul_one_div, mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- The *change* context set is dispreferred under any prior weighting it at most as much as
the context set that John smoked, which the common-ground prior does by design. -/
theorem now_change_lt (π : Finset World → ℕ) (hπ : π pastT ≠ 0) (h : π change ≤ π pastT)
    {α : ℝ} (hα : 0 < α) :
    (listener .now π α notStopped).real {(.FT, change)}
      < (listener .now π α notStopped).real {(.TT, pastT)} := by
  have hx := half_rpow_lt_one hα
  have hx0 : (0 : ℝ) < (1 / 2 : ℝ) ^ α := by positivity
  have hπ' : (0 : ℝ) < π pastT := by exact_mod_cast Nat.pos_of_ne_zero hπ
  have h' : (π change : ℝ) ≤ π pastT := by exact_mod_cast h
  rw [listener_lt_iff .now π _ _ _ _ (by decide) (by decide), share_C hα, share_A hα,
    mul_one_div, mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The universe is outrun at every rationality of at least one under any prior weighting it
under three halves of the context set that John smoked, since there the utterance leaves a third
of the answer open. -/
theorem now_universe_lt (π : Finset World → ℕ) (hπ : π pastT ≠ 0)
    (h : 2 * π Finset.univ ≤ 3 * π pastT) {α : ℝ} (hα : 1 ≤ α) :
    (listener .now π α notStopped).real {(.TT, Finset.univ)}
      < (listener .now π α notStopped).real {(.TT, pastT)} := by
  have hα0 : 0 < α := by linarith
  have hx0 : (0 : ℝ) < (1 / 2 : ℝ) ^ α := by positivity
  have hy0 : (0 : ℝ) < (2 / 3 : ℝ) ^ α := by positivity
  have hz0 : (0 : ℝ) < (1 / 3 : ℝ) ^ α := by positivity
  have hy : (2 / 3 : ℝ) ^ α ≤ 2 / 3 := by
    have := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num) hα
    rwa [Real.rpow_one] at this
  have hπ' : (0 : ℝ) < π pastT := by exact_mod_cast Nat.pos_of_ne_zero hπ
  have hU : (0 : ℝ) ≤ π Finset.univ := by positivity
  have h' : 2 * (π Finset.univ : ℝ) ≤ 3 * π pastT := by exact_mod_cast h
  have h1 : (π Finset.univ : ℝ) * (2 / 3 : ℝ) ^ α ≤ π pastT := by nlinarith
  rw [listener_lt_iff .now π _ _ _ _ (by decide) (by decide), share_D hα0, share_A hα0,
    mul_div_assoc', mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The common-ground prior (8) meets the hypotheses, since the observed context sets outweigh
*change* and the universe weighs under three halves of a single observation. -/
theorem cgWeight_facts :
    cgWeight pastT ≠ 0 ∧ cgWeight nowF ≤ cgWeight pastT ∧ cgWeight nowT ≤ cgWeight pastT ∧
      cgWeight change ≤ cgWeight pastT ∧ 2 * cgWeight Finset.univ ≤ 3 * cgWeight pastT := by
  decide

/-- Under the common-ground prior and the question whether John smokes now, the world in which
he still smokes with the context set that he smoked beats every competitor the paper discusses
at every rationality of at least one. Projection is context-set inference (Figure 3). -/
theorem now_cg_mode {α : ℝ} (hα : 1 ≤ α) :
    (listener .now cgWeight α notStopped).real {(.FF, nowF)}
        < (listener .now cgWeight α notStopped).real {(.TT, pastT)} ∧
      (listener .now cgWeight α notStopped).real {(.TT, nowT)}
        < (listener .now cgWeight α notStopped).real {(.TT, pastT)} ∧
      (listener .now cgWeight α notStopped).real {(.FT, change)}
        < (listener .now cgWeight α notStopped).real {(.TT, pastT)} ∧
      (listener .now cgWeight α notStopped).real {(.TT, Finset.univ)}
        < (listener .now cgWeight α notStopped).real {(.TT, pastT)} :=
  let ⟨h0, h1, h2, h3, h4⟩ := cgWeight_facts
  ⟨(now_settled_lt _ h0 h1 h2 (by linarith)).1, (now_settled_lt _ h0 h1 h2 (by linarith)).2,
    now_change_lt _ h0 h3 (by linarith), now_universe_lt _ h0 h4 hα⟩

end QingGoodmanLassiter2016
