module

public import Linglib.Pragmatics.Probabilistic.Recursion
public import Linglib.Pragmatics.Agent.Basic
public import Linglib.Core.Probability.UniformOn
public import Minimemo.Examples.RSA

/-!
# Chandra, Chen, Tenenbaum and Ragan-Kelley (2025): A language for reasoning about reasoning

memo is a programming language for models in which agents reason about agents. A model is a
sequence of statements, each attributed to an agent: an agent *chooses* a value with probability
proportional to a weight, *observes* a choice of another agent, and *thinks* that other agents
choose and observe. A model returns an array.

The paper's first model is a reference game. A speaker has one of three referents in mind, a green
square, a green circle and a pink circle, and says one of *green*, *pink*, *square* and *round*. A
listener at depth zero thinks that the speaker chooses among the utterances that describe the
referent. A listener at a greater depth thinks that the speaker chooses such an utterance with
weight the exponential of `β` times the probability that the listener one depth below gives the
referent on hearing it.

Here the speaker is an agent who knows the referent and values a true utterance at that
probability, and the listener holds a uniform prior and applies Bayes' rule to the speaker's
policy. [The memo program realizes this listener](##realizes_listenerAt), at every depth and
every positive `β`: the kernel of its array is her kernel. A program realizes at most one kernel,
so the programs that realize her are equivalent to one another, and what is proved of the
program's array is proved of her: [her probability of the green square on hearing *green* falls
with the depth to a limit](##tendsto_listenerAt). At depth zero [she is the literal
listener](##listenerAt_zero_real).

The speaker of the Rational Speech Acts model soft-maximizes the logarithm of the listener's
probability, where this speaker soft-maximizes the probability. At the first level of that
recursion, on hearing *green*, [the listener gives the green square the probability
`2 / (3 + 2 ^ α)`](##recurse_literalListener_real), where this one gives it
`2 / (3 + exp (β / 2))`. So at depth one [the two listeners are the same exactly when
`exp (β / 2) = 2 ^ α`](##listenerAt_one_eq_recurse_iff).

## Implementation notes

The memo program is taken from the library minimemo, which gives memo programs their arrays in
Lean and proves the array of this program at every depth. The array has an axis for the
utterance and an axis for the referent, and is stored in row-major order.

The denotation of an utterance is the set of referents that it describes. In the program it is an
outside function with the values one and zero.

The speaker at depth zero values every true utterance at zero and has the rationality one, so
that her policy is uniform on the true utterances. The results hold for a positive `β`: at zero
the policy of an agent is uniform on all utterances, where the program's speaker still chooses
among the true ones.

## TODO

* With `β` equal to one the paper prints `0.43` for the green square on hearing *green* at depth
  one. Here that probability is `2 / (3 + exp (1 / 2))`; the decimal bound is not proved.
* The paper fits `β` to the choices of people in the reference game and compares depths zero and
  one. The data are not here.
* The two listeners should differ at depth two for every `α` and `β`; only depth one is compared.

## References

* [chandra-etal-2025]
* [frank-goodman-2012]
* [bergen-levy-goodman-2016]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace ChandraEtAl2025

/-- The utterances: two colours and two shapes. -/
inductive Utterance where
  | green | pink | square | round
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ ↦ trivial⟩

/-- The referents: a green square, a green circle and a pink circle. -/
inductive Referent where
  | greenSquare | greenCircle | pinkCircle
  deriving DecidableEq, Fintype

instance : MeasurableSpace Referent := ⊤
instance : Nonempty Referent := ⟨.greenSquare⟩
instance : DiscreteMeasurableSpace Referent := ⟨fun _ ↦ trivial⟩

/-- The referents that an utterance describes. -/
def sem : Utterance → Set Referent
  | .green => {.greenSquare, .greenCircle}
  | .pink => {.pinkCircle}
  | .square => {.greenSquare}
  | .round => {.greenCircle, .pinkCircle}

instance (u : Utterance) (r : Referent) : Decidable (r ∈ sem u) := by
  cases u <;> cases r <;> simp only [sem, Set.mem_insert_iff, Set.mem_singleton_iff, reduceCtorEq,
    or_self, or_false, or_true] <;> infer_instance

/-- A speaker who knows the referent and values a true utterance at `v u r`. -/
noncomputable def agent (v : Utterance → Referent → ℝ) : Agent Referent Referent Utterance where
  belief := Kernel.id
  utility r u := if r ∈ sem u then (v u r : EReal) else ⊥

private theorem feasible_agent (v : Utterance → Referent → ℝ) (r : Referent) (u : Utterance) :
    (agent v).Feasible r u ↔ r ∈ sem u := by
  have : {s | (agent v).utility s u = ⊥} = (sem u)ᶜ := by
    ext s
    by_cases h : s ∈ sem u <;> simp [agent, h]
  rw [Agent.Feasible, this, show (agent v).belief r = Measure.dirac r from rfl,
    Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
  by_cases h : r ∈ sem u <;> simp [h]

private theorem value_agent (v : Utterance → Referent → ℝ) (r : Referent) (u : Utterance)
    (h : r ∈ sem u) : (agent v).value r u = v u r := by
  rw [Agent.value, show (agent v).belief r = Measure.dirac r from rfl, integral_dirac]
  simp [agent, h]

/-- The weight that memo's speaker gives an utterance: the exponential of `β` times its value where
it describes the referent, and zero elsewhere. -/
noncomputable def weight (β : ℝ) (v : Utterance → Referent → ℝ) (r : Referent) (u : Utterance) :
    ℝ :=
  if r ∈ sem u then Real.exp (β * v u r) else 0

-- the policy of the agent is memo's `chooses` with these weights
theorem policy_agent_real {β : ℝ} (hβ : 0 < β) (v : Utterance → Referent → ℝ) (r : Referent)
    (u : Utterance) :
    ((agent v).policy β r).real {u} = weight β v r u / ∑ u', weight β v r u' := by
  classical
  have hw (u' : Utterance) : EReal.exp (β * if (agent v).Feasible r u' then
      ((agent v).value r u' : EReal) else ⊥) = ENNReal.ofReal (weight β v r u') := by
    by_cases h : r ∈ sem u'
    · simp only [(feasible_agent v r u').2 h, ↓reduceIte, value_agent v r u' h, weight, h]
      rw [← EReal.coe_mul, EReal.exp_coe]
    · simp only [mt (feasible_agent v r u').1 h, ↓reduceIte, weight, h, ENNReal.ofReal_zero]
      rw [EReal.coe_mul_bot_of_pos hβ, EReal.exp_bot]
  rw [Agent.policy, Kernel.softmax, Kernel.ofWeights_real_singleton _ _ fun b ↦ by
    rw [hw]; exact ENNReal.ofReal_ne_top]
  simp_rw [hw]
  have hnn (u' : Utterance) : 0 ≤ weight β v r u' := by
    unfold weight; split_ifs <;> positivity
  simp_rw [ENNReal.toReal_ofReal (hnn _)]

private theorem sum_utterance (f : Utterance → ℝ) :
    ∑ u, f u = f .green + f .pink + f .square + f .round := by
  rw [show (Finset.univ : Finset Utterance) = {.green, .pink, .square, .round} by decide]
  simp [Finset.sum_insert, add_assoc]

private theorem sum_referent (f : Referent → ℝ) :
    ∑ r, f r = f .greenSquare + f .greenCircle + f .pinkCircle := by
  rw [show (Finset.univ : Finset Referent) = {.greenSquare, .greenCircle, .pinkCircle} by decide]
  simp [Finset.sum_insert, add_assoc]

/-- The listener of a speaker who values a true utterance at `v`, under a uniform prior. -/
noncomputable def hear (β : ℝ) (v : Utterance → Referent → ℝ) : Kernel Utterance Referent :=
  listener (uniformOn Set.univ) ((agent v).policy β)

/-- The probabilities of a listener who, on hearing *green*, gives the green square the
probability `p`, and on hearing *round* gives the pink circle the probability `p`. -/
def table (p : ℝ) : Utterance → Referent → ℝ
  | .green, .greenSquare => p
  | .green, .greenCircle => 1 - p
  | .pink, .pinkCircle => 1
  | .square, .greenSquare => 1
  | .round, .greenCircle => 1 - p
  | .round, .pinkCircle => p
  | _, _ => 0

private theorem hear_real {β : ℝ} (hβ : 0 < β) (v : Utterance → Referent → ℝ) (u : Utterance)
    (r : Referent) :
    (hear β v u).real {r} = (weight β v r u / ∑ u', weight β v r u') /
      ∑ r', weight β v r' u / ∑ u', weight β v r' u' := by
  have h := listener_uniformOn_univ_real_finset (fun r ↦ (agent v).policy β r) u {r}
  simp only [Finset.coe_singleton, Finset.sum_singleton, policy_agent_real hβ] at h
  exact h

-- Bayes' rule on a channel whose weights are symmetric between the two ambiguous utterances: the
-- green square has the weights `a` for *green* and `b` for *square*, the pink circle `a` for
-- *round* and `b` for *pink*, and the green circle `d` for each of *green* and *round*
private theorem posterior_table (W : Referent → Utterance → ℝ) {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) (h0 : ∀ r u, r ∉ sem u → W r u = 0)
    (h1 : W .greenSquare .green = a) (h2 : W .greenSquare .square = b)
    (h3 : W .greenCircle .green = d) (h4 : W .greenCircle .round = d)
    (h5 : W .pinkCircle .pink = b) (h6 : W .pinkCircle .round = a) (u : Utterance)
    (r : Referent) :
    (W r u / ∑ u', W r u') / ∑ r', W r' u / ∑ u', W r' u' = table (2 * a / (3 * a + b)) u r := by
  have e1 := h0 .greenSquare .pink (by simp [sem])
  have e2 := h0 .greenSquare .round (by simp [sem])
  have e3 := h0 .greenCircle .pink (by simp [sem])
  have e4 := h0 .greenCircle .square (by simp [sem])
  have e5 := h0 .pinkCircle .green (by simp [sem])
  have e6 := h0 .pinkCircle .square (by simp [sem])
  cases u <;> cases r <;>
    simp [sum_utterance, sum_referent, table, h1, h2, h3, h4, h5, h6, e1, e2, e3, e4, e5, e6] <;>
    first | done | exact ⟨hb.ne', by positivity⟩ | (field_simp; ring)

private theorem hear_real_table {β : ℝ} (hβ : 0 < β) (v : Utterance → Referent → ℝ) {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (h1 : Real.exp (β * v .green .greenSquare) = a)
    (h2 : Real.exp (β * v .square .greenSquare) = b)
    (h3 : Real.exp (β * v .green .greenCircle) = d)
    (h4 : Real.exp (β * v .round .greenCircle) = d)
    (h5 : Real.exp (β * v .pink .pinkCircle) = b) (h6 : Real.exp (β * v .round .pinkCircle) = a)
    (u : Utterance) (r : Referent) :
    (hear β v u).real {r} = table (2 * a / (3 * a + b)) u r := by
  rw [hear_real hβ]
  exact posterior_table (weight β v) ha hb hd (fun r u h ↦ by simp [weight, h])
    (by simp [weight, sem, h1]) (by simp [weight, sem, h2]) (by simp [weight, sem, h3])
    (by simp [weight, sem, h4]) (by simp [weight, sem, h5]) (by simp [weight, sem, h6]) u r

/-- The listener at depth `t`. At depth zero the speaker values every true utterance alike. At a
greater depth the speaker values a true utterance at the probability that the listener one depth
below gives the referent on hearing it. -/
noncomputable def listenerAt (β : ℝ) : ℕ → Kernel Utterance Referent
  | 0 => hear 1 fun _ _ ↦ 0
  | t + 1 => hear β fun u r ↦ (listenerAt β t u).real {r}

instance (β : ℝ) (t : ℕ) : IsFiniteKernel (listenerAt β t) := by
  cases t <;> exact inferInstanceAs (IsFiniteKernel (listener _ _))

-- the listener at every depth, by the recursion on the probability of the green square
theorem listenerAt_real {β : ℝ} (hβ : 0 < β) (t : ℕ) (u : Utterance) (r : Referent) :
    (listenerAt β t u).real {r} = table (Memo.RSA.prob β t) u r := by
  induction t generalizing u r with
  | zero =>
    rw [listenerAt, hear_real_table one_pos _ one_pos one_pos one_pos (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp), Memo.RSA.prob]
    norm_num
  | succ t ih =>
    rw [listenerAt, hear_real_table hβ _ (Real.exp_pos (β * Memo.RSA.prob β t))
      (Real.exp_pos (β * 1)) (Real.exp_pos (β * (1 - Memo.RSA.prob β t)))
      (by rw [ih]; rfl) (by rw [ih]; rfl) (by rw [ih]; rfl) (by rw [ih]; rfl) (by rw [ih]; rfl)
      (by rw [ih]; rfl), Memo.RSA.prob]

/-- The position of an utterance on the first axis of memo's array. -/
def Utterance.pos : Utterance → ℕ
  | .green => 0 | .pink => 1 | .square => 2 | .round => 3

/-- The position of a referent on the second axis of memo's array. -/
def Referent.pos : Referent → ℕ
  | .greenSquare => 0 | .greenCircle => 1 | .pinkCircle => 2

/-- A memo program **realizes** a kernel when the kernel of its array, from the positions of what
is given to the positions of what is reported, is that kernel at the values with those positions.
Programs that realize one kernel are equivalent, and so are agents whose policies are realized by
one program. -/
def Realizes {O A : Type*} [MeasurableSpace O] [MeasurableSpace A] (k : Kernel ℕ ℕ)
    (heard : O → ℕ) (chosen : A → ℕ) (κ : Kernel O A) : Prop :=
  ∀ o a, k (heard o) {chosen a} = κ o {a}

-- a memo program realizes at most one kernel
theorem Realizes.unique {O A : Type*} [MeasurableSpace O] [MeasurableSpace A] [Countable A]
    [MeasurableSingletonClass A] {k : Kernel ℕ ℕ} {heard : O → ℕ} {chosen : A → ℕ}
    {κ₁ κ₂ : Kernel O A} (h₁ : Realizes k heard chosen κ₁) (h₂ : Realizes k heard chosen κ₂) :
    κ₁ = κ₂ :=
  Kernel.ext fun o ↦ Measure.ext_of_singleton fun a ↦ (h₁ o a).symm.trans (h₂ o a)

/-- **The memo program realizes the listener.** The program of Figure 1 at depth `t` realizes the
listener at depth `t`: its array has, at an utterance and a referent, the probability that she
gives the referent on hearing the utterance. -/
theorem realizes_listenerAt {β : ℝ} (hβ : 0 < β) (t : ℕ) :
    Realizes (Memo.RSA.family.kernel (Memo.NaiveListener.domOf ℝ) (Memo.RSA.callOf β) (t + 1) t)
      Utterance.pos Referent.pos (listenerAt β t) := fun u r ↦ by
  rw [Memo.RSA.kernel_family, ← ofReal_measureReal (measure_ne_top _ _), listenerAt_real hβ]
  cases u <;> cases r <;> rfl

/-- What memo's model does in the limit, the listener does: as the depth grows, the probability
that she gives the green square on hearing *green* tends to the greatest `p` with
`p = 2 / (3 + exp (β * (1 - p)))`. -/
theorem tendsto_listenerAt {β : ℝ} (hβ : 0 < β) :
    Filter.Tendsto (fun t ↦ (listenerAt β t .green).real {.greenSquare}) Filter.atTop
      (nhds (Memo.RSA.limit β)) := by
  simp_rw [listenerAt_real hβ]
  exact Memo.RSA.tendsto_prob hβ.le

/-! ### The speaker of the Rational Speech Acts model -/

private theorem literalListener_real (u : Utterance) (r : Referent) :
    (literalListener (uniformOn Set.univ) sem u).real {r} = table (1 / 2) u r := by
  have h := listener_uniformOn_univ_real_finset (truthful sem) u {r}
  simp only [Finset.coe_singleton, Finset.sum_singleton, measureReal_def,
    truthful_apply_singleton] at h
  rw [show literalListener (uniformOn Set.univ) sem = listener (uniformOn Set.univ) (truthful sem)
    from rfl, measureReal_def, h]
  cases u <;> cases r <;> simp [sum_referent, sem, table, Set.indicator] <;> norm_num

/-- The listener at depth zero is the literal listener: Section 2.2. -/
theorem listenerAt_zero_real {β : ℝ} (hβ : 0 < β) (u : Utterance) (r : Referent) :
    (listenerAt β 0 u).real {r} = (literalListener (uniformOn Set.univ) sem u).real {r} := by
  rw [listenerAt_real hβ, literalListener_real, Memo.RSA.prob]

/-- The listener at the first level of the recursion of the Rational Speech Acts model, whose
speaker has rationality `α`, gives the green square the probability `2 / (3 + 2 ^ α)` on hearing
*green*. -/
theorem recurse_literalListener_real {α : ℝ} (hα : 0 < α) (u : Utterance) (r : Referent) :
    (recurse (uniformOn Set.univ) Kernel.id Measure.dirac α 0
      (literalListener (uniformOn Set.univ) sem) u).real {r} = table (2 / (3 + 2 ^ α)) u r := by
  have hL (u : Utterance) (r : Referent) :
      ((literalListener (uniformOn Set.univ) sem u {r}) ^ α).toReal = table (1 / 2) u r ^ α := by
    rw [← ENNReal.toReal_rpow, ← measureReal_def, literalListener_real]
  have h := listener_uniformOn_univ_real_finset
    (fun r ↦ speaker α (0 : Utterance → ℝ) (literalListener (uniformOn Set.univ) sem)
      Measure.dirac r) u {r}
  simp only [Finset.coe_singleton, Finset.sum_singleton,
    speaker_dirac_zero_real_singleton hα.le, hL] at h
  rw [recurse_id_dirac]
  refine h.trans ?_
  have ha : (0 : ℝ) < (1 / 2) ^ α := by positivity
  rw [posterior_table (fun r u ↦ table (1 / 2) u r ^ α) ha one_pos ha
    (fun r u hru ↦ by cases u <;> cases r <;> simp_all [sem, table, Real.zero_rpow hα.ne'])
    (by simp [table]) (by simp [table]) (by norm_num [table]) (by norm_num [table])
    (by simp [table]) (by simp [table])]
  congr 1
  rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]
  have h2 : (0 : ℝ) < 2 ^ α := by positivity
  field_simp

/-- At depth one the two speakers give the same listener exactly when `exp (β / 2) = 2 ^ α`: on
this array, the softmax of the listener's probability at `β` is the softmax of its logarithm at
`α`. -/
theorem listenerAt_one_eq_recurse_iff {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (listenerAt β 1 .green).real {.greenSquare} =
        (recurse (uniformOn Set.univ) Kernel.id Measure.dirac α 0
          (literalListener (uniformOn Set.univ) sem) .green).real {.greenSquare} ↔
      Real.exp (β / 2) = 2 ^ α := by
  rw [listenerAt_real hβ, recurse_literalListener_real hα, Memo.RSA.prob_succ, Memo.RSA.prob]
  simp only [table]
  have h2 : (0 : ℝ) < 2 ^ α := by positivity
  rw [show β * (1 - 1 / 2) = β / 2 by ring]
  have h3 := Real.exp_pos (β / 2)
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]

end ChandraEtAl2025
