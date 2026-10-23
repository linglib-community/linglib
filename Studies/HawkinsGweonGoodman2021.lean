module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Pragmatics.RSA.Basic

/-!
# Hawkins, Gweon and Goodman (2021): The division of labor in communication

This file formalizes the resource-rational model of perspective-taking of
[hawkins-gweon-goodman-2021] for the director–matcher task. A `Game` fixes the target, the
shared context, the graded meaning of Eq. 1 (a false description keeps a small mass `ε`)
and the prior over the object hidden behind an occluder. The egocentric speaker utility
`Game.egoUtility` (Eq. 3) rewards informativity for the literal listener over the shared
context; the asymmetry-aware utility `Game.asymUtility` (Eq. 2) averages it over the hidden
object; `Game.mixUtility` (Eq. 5) interpolates with the weight `wS`, and `Game.mixSpeaker`
is the corresponding score speaker of the kernel pipeline. On the listener's side
`Game.mixListener` (Eq. 6) mixes the literal listener over the speaker's view with the one
over the listener's own view, and `Game.rrSpeakerUtility` is the resource-rational
trade-off of Eq. 10 between the accuracy the best utterance earns and the linear cost of
perspective-taking.

`Game.gain_eq` decomposes the extra preference of the asymmetric over the egocentric
utility for a more specific description into a sum over hidden objects, from which
Appendix A's Theorem 1 follows when the two descriptions are equally informative over
the shared context (`Game.gain_pos_of_tie`), together with the preference of every mixture
speaker with `wS > 0` (`Game.mixSpeaker_prefers`). `Game.gain_neg_of_shared_hidden`
records that the theorem's premise cannot be dropped: a hidden object satisfying both
descriptions weakens the asymmetric speaker's relative preference.

## Implementation notes

* The literal listener `Game.L0` is the uniform prior on a finite context reweighted by the
  meaning of Eq. 1, and the speakers are `Kernel.softmax` over the single state of the
  fixed target.
* Appendix A's proof treats a hidden object that satisfies both descriptions as leaving
  the listener unchanged, which holds only when the two descriptions have the same mass
  over the shared context; `Game.gain_eq` makes the residual term explicit and
  `Game.gain_neg_of_shared_hidden` exhibits the failure. The paper's simulations, with a
  target that shape alone identifies in the shared context, satisfy the tie
  (`stimulus_tie`).
* The nested weights of Eqs. 7–9 and the listener's resource-rational utility over the
  pragmatic listener are not formalized; the speaker's Eq. 10 uses the literal listener of
  Eq. 6 with a discrete uniform prior over the listener weight, whose expectation is the
  midpoint (`Game.rrSpeakerUtility_eq`).

## TODO

* Eqs. 7–9: agents reasoning about the partner's weight, and the interior optimum of §2.4.
* Appendix B: the listener's posterior over the speaker's weight from observed utterances.

## References

* [hawkins-gweon-goodman-2021]
* [keysar-etal-2003]
-/

@[expose] public section

namespace HawkinsGweonGoodman2021

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-! ### The model (§2) -/

/-- A director–matcher game: utterances `U` describe objects `O`; the speaker refers to
`target` in the shared `context`, with the listener possibly seeing one more object drawn
from `hidden`. -/
structure Game (O U : Type*) where
  /-- Whether an utterance is true of an object. -/
  applies : U → O → Prop
  /-- The target of reference. -/
  target : O
  /-- The shared context: the objects both agents see. -/
  context : Finset O
  /-- The prior over the object hidden behind an occluder. -/
  hidden : O → ℝ
  /-- The production cost of an utterance. -/
  cost : U → ℝ
  /-- The mass a false description keeps in Eq. 1. -/
  ε : ℝ

namespace Game

variable {O U : Type*} (g : Game O U) [∀ u, DecidablePred (g.applies u)]

/-- The graded meaning of Eq. 1: `1` where the utterance is true, `ε` where it is false. -/
noncomputable def meaning (u : U) (o : O) : ℝ := if g.applies u o then 1 else g.ε

/-- The total meaning mass of an utterance over a context. -/
noncomputable def mass (S : Finset O) (u : U) : ℝ := ∑ o ∈ S, g.meaning u o

/-- The literal listener over a context (Eq. 1): the uniform prior on the context
reweighted by the meaning. -/
noncomputable def L0 (S : Finset O) (u : U) (o : O) : ℝ := g.meaning u o / g.mass S u

/-- (3): the egocentric speaker utility, informativity for the literal listener over the
shared context less cost. -/
noncomputable def egoUtility (u : U) : ℝ := Real.log (g.L0 g.context u g.target) - g.cost u

theorem meaning_pos (hε : 0 < g.ε) (u : U) (o : O) : 0 < g.meaning u o := by
  unfold meaning; split_ifs <;> linarith

theorem meaning_le_one (hε1 : g.ε ≤ 1) (u : U) (o : O) : g.meaning u o ≤ 1 := by
  unfold meaning; split_ifs <;> linarith

theorem mass_pos (hε : 0 < g.ε) {S : Finset O} (hS : S.Nonempty) (u : U) : 0 < g.mass S u :=
  sum_pos (fun o _ => g.meaning_pos hε u o) hS

theorem meaning_le_of_specific (hε1 : g.ε ≤ 1) {u₀ u₁ : U}
    (hspec : ∀ o, g.applies u₀ o → g.applies u₁ o) (o : O) :
    g.meaning u₀ o ≤ g.meaning u₁ o := by
  unfold meaning
  by_cases h₀ : g.applies u₀ o
  · simp [h₀, hspec o h₀]
  · split_ifs <;> linarith

theorem mass_congr {S : Finset O} {u₀ u₁ : U}
    (h : ∀ o ∈ S, g.applies u₀ o ↔ g.applies u₁ o) : g.mass S u₀ = g.mass S u₁ :=
  sum_congr rfl fun o ho => by simp [meaning, h o ho]

section Listener

variable [DecidableEq O]

/-- (6): the listener mixing the literal listener over the speaker's view (the
asymmetry-aware listener, which discounts its private object `h`) with the one over its own
view, with weight `wL`. -/
noncomputable def mixListener (h : O) (wL : ℝ) (u : U) (o : O) : ℝ :=
  wL * g.L0 g.context u o + (1 - wL) * g.L0 (insert h g.context) u o

theorem mass_insert_of_notMem {S : Finset O} {h : O} (hh : h ∉ S) (u : U) :
    g.mass (insert h S) u = g.meaning u h + g.mass S u :=
  sum_insert hh

theorem L0_insert_le (hε : 0 < g.ε) (u : U) (o h : O) (hh : h ∉ g.context)
    (hc : g.context.Nonempty) : g.L0 (insert h g.context) u o ≤ g.L0 g.context u o := by
  unfold L0
  rw [g.mass_insert_of_notMem hh]
  exact div_le_div_of_nonneg_left (g.meaning_pos hε u o).le (g.mass_pos hε hc u)
    (le_add_of_nonneg_left (g.meaning_pos hε u h).le)

theorem mixListener_target_mono (hε : 0 < g.ε) (u : U) (h : O) (hh : h ∉ g.context)
    (hc : g.context.Nonempty) : Monotone fun wL => g.mixListener h wL u g.target := by
  intro a b hab
  simp only [mixListener]
  nlinarith [g.L0_insert_le hε u g.target h hh hc]

end Listener

variable [Fintype O]

/-- (2): the asymmetry-aware speaker utility, informativity averaged over the object the
listener may see behind the occluder. -/
noncomputable def asymUtility (u : U) : ℝ :=
  ∑ h, g.hidden h * Real.log (g.meaning u g.target / (g.meaning u h + g.mass g.context u)) -
    g.cost u

/-- (5): the mixture utility with perspective-taking weight `wS`. -/
noncomputable def mixUtility (wS : ℝ) (u : U) : ℝ :=
  wS * g.asymUtility u + (1 - wS) * g.egoUtility u

theorem mixUtility_zero (u : U) : g.mixUtility 0 u = g.egoUtility u := by simp [mixUtility]

theorem mixUtility_one (u : U) : g.mixUtility 1 u = g.asymUtility u := by simp [mixUtility]

/-! ### Appendix A -/

/-- The extra preference of the asymmetric over the egocentric utility for `u₀` against
`u₁`, decomposed over the hidden object: each hidden object contributes the log-ratio of
how much it dilutes the two descriptions. -/
theorem gain_eq (hε : 0 < g.ε) (hc : g.context.Nonempty) (hsum : ∑ h, g.hidden h = 1)
    (u₀ u₁ : U) :
    (g.asymUtility u₀ - g.asymUtility u₁) - (g.egoUtility u₀ - g.egoUtility u₁) =
      ∑ h, g.hidden h *
        (Real.log (1 + g.meaning u₁ h / g.mass g.context u₁) -
          Real.log (1 + g.meaning u₀ h / g.mass g.context u₀)) := by
  have hm : ∀ u o, g.meaning u o ≠ 0 := fun u o => (g.meaning_pos hε u o).ne'
  have hS : ∀ u, g.mass g.context u ≠ 0 := fun u => (g.mass_pos hε hc u).ne'
  have hd : ∀ u h, g.meaning u h + g.mass g.context u ≠ 0 := fun u h =>
    (add_pos (g.meaning_pos hε u h) (g.mass_pos hε hc u)).ne'
  have key : ∀ u h, Real.log (g.meaning u g.target / (g.meaning u h + g.mass g.context u)) =
      Real.log (g.L0 g.context u g.target) -
        Real.log (1 + g.meaning u h / g.mass g.context u) := by
    intro u h
    have hpos1 : 1 + g.meaning u h / g.mass g.context u ≠ 0 :=
      (add_pos one_pos (div_pos (g.meaning_pos hε u h) (g.mass_pos hε hc u))).ne'
    have e : g.meaning u g.target / (g.meaning u h + g.mass g.context u) =
        g.meaning u g.target / g.mass g.context u / (1 + g.meaning u h / g.mass g.context u) := by
      field_simp [hS u, hd u h]
      rw [add_comm (g.mass g.context u), mul_div_assoc, div_self (hd u h), mul_one]
    rw [e, L0, Real.log_div (div_ne_zero (hm u g.target) (hS u)) hpos1]
  have expand : ∀ u, g.asymUtility u = Real.log (g.L0 g.context u g.target) -
      (∑ h, g.hidden h * Real.log (1 + g.meaning u h / g.mass g.context u)) - g.cost u := by
    intro u
    simp only [asymUtility, key, mul_sub, sum_sub_distrib, ← sum_mul, hsum, one_mul]
  rw [expand, expand]
  simp only [egoUtility, mul_sub, sum_sub_distrib]
  ring

/-- Under a tie in context mass, a more specific `u₀` gains more under the asymmetric than the
egocentric utility when some hidden object satisfies only `u₁` (Appendix A, Theorem 1). -/
theorem gain_pos_of_tie (hε : 0 < g.ε) (hε1 : g.ε < 1) (hc : g.context.Nonempty)
    (hp : ∀ h, 0 ≤ g.hidden h) (hsum : ∑ h, g.hidden h = 1) {u₀ u₁ : U}
    (hspec : ∀ o, g.applies u₀ o → g.applies u₁ o)
    (htie : g.mass g.context u₀ = g.mass g.context u₁)
    (hstar : ∃ h, g.applies u₁ h ∧ ¬ g.applies u₀ h ∧ 0 < g.hidden h) :
    g.egoUtility u₀ - g.egoUtility u₁ < g.asymUtility u₀ - g.asymUtility u₁ := by
  rw [← sub_pos, gain_eq g hε hc hsum, htie]
  obtain ⟨h₀, h₁, h₂, hpos⟩ := hstar
  have hS := g.mass_pos hε hc u₁
  have hpos' : ∀ u h, 0 < 1 + g.meaning u h / g.mass g.context u₁ := fun u h =>
    add_pos one_pos (div_pos (g.meaning_pos hε u h) hS)
  have hterm : ∀ h, 0 ≤ g.hidden h *
      (Real.log (1 + g.meaning u₁ h / g.mass g.context u₁) -
        Real.log (1 + g.meaning u₀ h / g.mass g.context u₁)) := fun h =>
    mul_nonneg (hp h) (sub_nonneg.2 (Real.log_le_log (hpos' u₀ h)
      (by gcongr; exact g.meaning_le_of_specific hε1.le hspec h)))
  refine lt_of_lt_of_le ?_ (single_le_sum (fun h _ => hterm h) (mem_univ h₀))
  refine mul_pos hpos (sub_pos.2 (Real.log_lt_log (hpos' u₀ h₀) ?_))
  have : g.meaning u₀ h₀ < g.meaning u₁ h₀ := by simp [meaning, h₁, h₂, hε1]
  gcongr

/-- When every likely hidden object satisfies both descriptions and `u₀` is narrower in context, the
asymmetric utility favours `u₀` less than the egocentric does (Appendix A). -/
theorem gain_neg_of_shared_hidden (hε : 0 < g.ε) (hc : g.context.Nonempty)
    (hp : ∀ h, 0 ≤ g.hidden h) (hsum : ∑ h, g.hidden h = 1) {u₀ u₁ : U}
    (hshared : ∀ h, 0 < g.hidden h → g.applies u₀ h ∧ g.applies u₁ h)
    (hlt : g.mass g.context u₀ < g.mass g.context u₁) :
    g.asymUtility u₀ - g.asymUtility u₁ < g.egoUtility u₀ - g.egoUtility u₁ := by
  rw [← sub_neg, gain_eq g hε hc hsum]
  have hS₀ := g.mass_pos hε hc u₀
  have hS₁ := g.mass_pos hε hc u₁
  have hterm : ∀ h, g.hidden h *
      (Real.log (1 + g.meaning u₁ h / g.mass g.context u₁) -
        Real.log (1 + g.meaning u₀ h / g.mass g.context u₀)) ≤ 0 := by
    intro h
    rcases (hp h).lt_or_eq with hpos | hzero
    · obtain ⟨h₀, h₁⟩ := hshared h hpos
      have hm : g.meaning u₀ h = 1 := by simp [meaning, h₀]
      have hm' : g.meaning u₁ h = 1 := by simp [meaning, h₁]
      rw [hm, hm']
      refine mul_nonpos_of_nonneg_of_nonpos hpos.le (sub_nonpos.2 (Real.log_le_log
        (add_pos one_pos (div_pos one_pos hS₁)) ?_))
      gcongr
    · rw [← hzero, zero_mul]
  obtain ⟨h₀, hpos⟩ : ∃ h, 0 < g.hidden h := by
    by_contra hnone
    have : ∑ h, g.hidden h = 0 :=
      sum_eq_zero fun h _ => le_antisymm (not_lt.1 fun hlt => hnone ⟨h, hlt⟩) (hp h)
    linarith
  obtain ⟨hh₀, hh₁⟩ := hshared h₀ hpos
  have hneg : g.hidden h₀ *
      (Real.log (1 + g.meaning u₁ h₀ / g.mass g.context u₁) -
        Real.log (1 + g.meaning u₀ h₀ / g.mass g.context u₀)) < 0 := by
    have hm : g.meaning u₀ h₀ = 1 := by simp [meaning, hh₀]
    have hm' : g.meaning u₁ h₀ = 1 := by simp [meaning, hh₁]
    rw [hm, hm']
    refine mul_neg_of_pos_of_neg hpos (sub_neg.2 (Real.log_lt_log
      (add_pos one_pos (div_pos one_pos hS₁)) ?_))
    gcongr
  exact (sum_lt_sum (fun h _ => hterm h) ⟨h₀, mem_univ _, hneg⟩).trans_eq sum_const_zero

/-! ### The resource-rational speaker (§2.4) -/

section ResourceRational

variable [DecidableEq O]

/-- The expected accuracy of an utterance for a listener of weight `wL`, averaged over the
hidden object. -/
noncomputable def accuracy (u : U) (wL : ℝ) : ℝ :=
  ∑ h, g.hidden h * g.mixListener h wL u g.target

theorem accuracy_eq (u : U) (wL : ℝ) :
    g.accuracy u wL = wL * (∑ h, g.hidden h * g.L0 g.context u g.target) +
      (1 - wL) * ∑ h, g.hidden h * g.L0 (insert h g.context) u g.target := by
  simp only [accuracy, mixListener, mul_sum]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun h _ => by ring

variable [Fintype U] [Nonempty U]

/-- The utterance the mixture speaker of weight `wS` prefers, `u*` of Eq. 10. -/
noncomputable def best (wS : ℝ) : U :=
  Classical.choose (exists_max_image univ (g.mixUtility wS) univ_nonempty)

omit [DecidableEq O] in
theorem best_isMax (wS : ℝ) (u : U) : g.mixUtility wS u ≤ g.mixUtility wS (g.best wS) :=
  (Classical.choose_spec (exists_max_image univ (g.mixUtility wS) univ_nonempty)).2 u
    (mem_univ u)

/-- (10): the speaker's resource-rational utility, the accuracy of its preferred utterance
under a listener weight drawn uniformly from the five-point grid, less the linear cost
`β · wS` of perspective-taking. -/
noncomputable def rrSpeakerUtility (β wS : ℝ) : ℝ :=
  (1 / 5 : ℝ) * ∑ k ∈ range 5, g.accuracy (g.best wS) ((k : ℝ) / 4) - β * wS

theorem rrSpeakerUtility_eq (β wS : ℝ) :
    g.rrSpeakerUtility β wS = g.accuracy (g.best wS) (1 / 2) - β * wS := by
  simp only [rrSpeakerUtility, accuracy_eq, sum_range_succ, sum_range_zero]
  push_cast
  ring

end ResourceRational

/-! ### Speakers of the kernel pipeline -/

variable [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]

/-- (1), (5): the mixture speaker with rationality `α` and perspective-taking weight `wS`,
a score speaker over the single state of the fixed target. -/
noncomputable def mixSpeaker (α wS : ℝ) : Kernel Unit U :=
  Kernel.softmax fun _ u => ((α * g.mixUtility wS u : ℝ) : EReal)

theorem mixSpeaker_lt_iff {α : ℝ} (hα : 0 < α) (wS : ℝ) {u u' : U} :
    (g.mixSpeaker α wS ()).real {u} < (g.mixSpeaker α wS ()).real {u'} ↔
      g.mixUtility wS u < g.mixUtility wS u' := by
  rw [mixSpeaker, Kernel.softmax_real_singleton_lt_iff
    (score := fun _ u => ((α * g.mixUtility wS u : ℝ) : EReal)) (fun _ => EReal.coe_ne_top _)
    ⟨u, EReal.coe_ne_bot _⟩, EReal.coe_lt_coe_iff]
  exact ⟨fun h => lt_of_mul_lt_mul_left h hα.le, fun h => mul_lt_mul_of_pos_left h hα⟩

/-- Under the tie of `gain_pos_of_tie`, if the egocentric speaker does not disprefer the more
specific description, every mixture speaker with `wS > 0` prefers it (Appendix A). -/
theorem mixSpeaker_prefers (hε : 0 < g.ε) (hε1 : g.ε < 1) (hc : g.context.Nonempty)
    (hp : ∀ h, 0 ≤ g.hidden h) (hsum : ∑ h, g.hidden h = 1) {u₀ u₁ : U}
    (hspec : ∀ o, g.applies u₀ o → g.applies u₁ o)
    (htie : g.mass g.context u₀ = g.mass g.context u₁)
    (hstar : ∃ h, g.applies u₁ h ∧ ¬ g.applies u₀ h ∧ 0 < g.hidden h)
    (hego : g.egoUtility u₁ ≤ g.egoUtility u₀) {α wS : ℝ} (hα : 0 < α) (hw : 0 < wS) :
    (g.mixSpeaker α wS ()).real {u₁} < (g.mixSpeaker α wS ()).real {u₀} := by
  rw [g.mixSpeaker_lt_iff hα]
  have := g.gain_pos_of_tie hε hε1 hc hp hsum hspec htie hstar
  simp only [mixUtility]
  nlinarith

end Game

/-! ### The stimulus of §2.4 -/

/-- The three features of the objects. -/
inductive Feature where
  | shape
  | color
  | texture
  deriving DecidableEq, Fintype, Repr

/-- An object as its profile of matches with the target on each feature. -/
abbrev Obj := Feature → Bool

/-- An utterance mentions a set of features. -/
abbrev Utt := Finset Feature

instance : MeasurableSpace Utt := ⊤
instance : MeasurableSingletonClass Utt := ⟨fun _ => trivial⟩

/-- The target matches itself on every feature. -/
def target : Obj := fun _ => true

/-- The distractor sharing the target's color and texture. -/
def d1 : Obj := fun f => decide (f ≠ .shape)

/-- The distractor matching the target on nothing. -/
def d2 : Obj := fun _ => false

/-- The prior over the hidden object's profile when each of the four values of a feature is
equally likely: a match on each feature with probability `1/4`, independently. -/
noncomputable def hiddenPrior (o : Obj) : ℝ :=
  ∏ f, if o f then (1 / 4 : ℝ) else 3 / 4

/-- The game of §2.4: the target with the two distractors of Fig. 1 in view, a hidden object
drawn from `hiddenPrior`, cost `c` per mentioned feature, and `ε = 1/100`. -/
noncomputable def stimulus (c : ℝ) : Game Obj Utt where
  applies u o := ∀ f ∈ u, o f = true
  target := target
  context := {target, d1, d2}
  hidden := hiddenPrior
  cost u := c * u.card
  ε := 1 / 100

instance (c : ℝ) : ∀ u, DecidablePred ((stimulus c).applies u) := fun u o =>
  inferInstanceAs (Decidable (∀ f ∈ u, o f = true))

theorem stimulus_hidden (c : ℝ) : (stimulus c).hidden = hiddenPrior := rfl

theorem hiddenPrior_pos (o : Obj) : 0 < hiddenPrior o :=
  prod_pos fun f _ => by split_ifs <;> norm_num

theorem hiddenPrior_nonneg (o : Obj) : 0 ≤ hiddenPrior o := (hiddenPrior_pos o).le

theorem sum_hiddenPrior : ∑ o : Obj, hiddenPrior o = 1 := by
  unfold hiddenPrior
  rw [← Fintype.prod_sum
    (f := fun (_ : Feature) (b : Bool) => if b = true then (1 / 4 : ℝ) else 3 / 4)]
  simp
  norm_num

theorem stimulus_tie (c : ℝ) :
    (stimulus c).mass (stimulus c).context {.shape, .color, .texture} =
      (stimulus c).mass (stimulus c).context {.shape} :=
  (stimulus c).mass_congr fun o ho => by
    simp only [stimulus, mem_insert, mem_singleton] at ho
    rcases ho with rfl | rfl | rfl
    · show (∀ f ∈ ({.shape, .color, .texture} : Finset Feature), target f = true) ↔
        ∀ f ∈ ({.shape} : Finset Feature), target f = true
      decide
    · show (∀ f ∈ ({.shape, .color, .texture} : Finset Feature), d1 f = true) ↔
        ∀ f ∈ ({.shape} : Finset Feature), d1 f = true
      decide
    · show (∀ f ∈ ({.shape, .color, .texture} : Finset Feature), d2 f = true) ↔
        ∀ f ∈ ({.shape} : Finset Feature), d2 f = true
      decide

/-- On the stimulus, a mixture speaker with `wS > 0` prefers the full description whenever the
egocentric speaker does not prefer the bare shape (§2.4.1). -/
theorem stimulus_prefers_full {c α wS : ℝ} (hα : 0 < α) (hw : 0 < wS)
    (hego : (stimulus c).egoUtility {.shape} ≤
      (stimulus c).egoUtility {.shape, .color, .texture}) :
    ((stimulus c).mixSpeaker α wS ()).real {({.shape} : Utt)} <
      ((stimulus c).mixSpeaker α wS ()).real {({.shape, .color, .texture} : Utt)} := by
  refine (stimulus c).mixSpeaker_prefers (by norm_num [stimulus]) (by norm_num [stimulus])
    ⟨target, by simp [stimulus]⟩ hiddenPrior_nonneg sum_hiddenPrior
    (fun o h f hf => h f (by simp only [mem_singleton] at hf; simp [hf])) (stimulus_tie c)
    ⟨fun f => decide (f = .shape), ?_, ?_, ?_⟩ hego hα hw
  · intro f hf; simp at hf; simp [hf]
  · intro h; have := h .color (by simp); simp at this
  · rw [stimulus_hidden]; exact hiddenPrior_pos _

end HawkinsGweonGoodman2021
