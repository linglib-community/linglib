module

public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Pragmatics.RSA.QUD
public import Linglib.Semantics.Degree.Granularity
public import Mathlib.Data.Rat.Floor

/-!
# Kao, Wu, Bergen and Goodman (2014): Nonliteral Understanding of Number Words

Kao, Wu, Bergen and Goodman model hyperbole on the RSA kernel pipeline. A meaning pairs a price
state with the speaker's affect; the literal listener conditions the prior on the price named, a
speaker with a communicative goal is informative about the goal's projection of the meaning and
pays a higher cost for sharp numbers, and the pragmatic listener marginalizes the goal.

## Main results

* `KaoWuEtAl2014.listener_ne_zero_iff`: a meaning receives positive posterior mass exactly when
  some goal of positive prior projects it into the cell of a meaning at which the utterance is
  literally true.
* `KaoWuEtAl2014.hyperbole`: a low price with affect is available under the affect goal.
* `KaoWuEtAl2014.literal_of_price_goals`, `KaoWuEtAl2014.halo_of_price_goals`: the comparison
  models of Fig. 2B.
* `KaoWuEtAl2014.approximate_prefers_round`: the halo effect of Fig. 3B rests on the cost.

## Implementation notes

Priors are arguments: the price prior and the conditional affect prior of Experiments 3a and 3b
enter as one probability measure on meanings, and the goal prior as a probability measure on
goals, uniform in the paper. The model's numerical fits (Figs. 2 to 5) rest on the raw priors
published as data rather than in the paper, and are not stated. The goals are the paper's, a
precision projection composed with a relevance projection, the two affect-only goals coinciding
(`project_affect`).

## References

* [kao-etal-2014-hyperbole]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace KaoWuEtAl2014

/-- The precision of a goal is exact, the paper's `f_e`, or approximate, `f_a`, which rounds the
price to the nearest multiple of ten. -/
inductive Precision
  | exact | approximate
  deriving DecidableEq, Repr, Fintype

/-- The price states of Materials and Methods are five round prices and their sharp neighbours. -/
inductive Price
  | p50 | p51 | p500 | p501 | p1000 | p1001 | p5000 | p5001 | p10000 | p10001
  deriving DecidableEq, Repr, Fintype

namespace Price

/-- The price in dollars. -/
def value : Price → ℕ
  | .p50 => 50 | .p51 => 51 | .p500 => 500 | .p501 => 501 | .p1000 => 1000
  | .p1001 => 1001 | .p5000 => 5000 | .p5001 => 5001 | .p10000 => 10000 | .p10001 => 10001

/-- A round price is divisible by ten. -/
def IsRound (p : Price) : Prop := 10 ∣ p.value

instance : DecidablePred IsRound := fun _ ↦ inferInstanceAs (Decidable (_ ∣ _))

/-- The nearest round price, the paper's `Round`. -/
def round : Price → Price
  | .p50 | .p51 => .p50 | .p500 | .p501 => .p500 | .p1000 | .p1001 => .p1000
  | .p5000 | .p5001 => .p5000 | .p10000 | .p10001 => .p10000

theorem isRound_round (p : Price) : p.round.IsRound := by cases p <;> decide

@[simp] theorem round_round (p : Price) : p.round.round = p.round := by cases p <;> rfl

theorem value_round (p : Price) :
    (p.round.value : ℚ) = Degree.representative 10 (p.value : ℚ) := by
  cases p <;> norm_num [round, value, Degree.representative]

/-- The precision projection `f` of a goal keeps the price exact or rounds it. -/
def project : Precision → Price → Price
  | .exact, p => p
  | .approximate, p => p.round

instance : MeasurableSpace Price := ⊤
instance : DiscreteMeasurableSpace Price := ⟨fun _ ↦ trivial⟩
instance : Nonempty Price := ⟨.p50⟩

end Price

/-- A meaning pairs the price state with whether the speaker has an affect about it, the paper's
`M = S × A` with `A = {0, 1}`. -/
abbrev Meaning := Price × Bool

/-- The relevance projection `r` of a goal keeps the price, the affect, or both. -/
inductive Relevance
  | price | affect | both
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Relevance := ⊤
instance : DiscreteMeasurableSpace Relevance := ⟨fun _ ↦ trivial⟩
instance : Nonempty Relevance := ⟨.price⟩
instance : MeasurableSpace Precision := ⊤
instance : DiscreteMeasurableSpace Precision := ⟨fun _ ↦ trivial⟩
instance : Nonempty Precision := ⟨.exact⟩

/-- A goal composes a precision projection with a relevance projection, `g(s, a) = r(f(s), a)`. -/
abbrev Goal := Precision × Relevance

/-- The projection of a goal keeps the price component, exact or rounded, and the affect component,
each when it is relevant. -/
def project (g : Goal) (m : Meaning) : Option Price × Option Bool :=
  (if g.2 = .affect then none else some (Price.project g.1 m.1),
    if g.2 = .price then none else some m.2)

theorem project_affect (f f' : Precision) : project (f, .affect) = project (f', .affect) :=
  rfl

/-- An utterance is true of a meaning when the price it names is the price state. -/
def sem (u : Price) : Set Meaning := {m | m.1 = u}

theorem mem_sem {u : Price} {m : Meaning} : m ∈ sem u ↔ m.1 = u := Iff.rfl

/-- The literal listener conditions the prior on the price named, eq. 9. -/
noncomputable def L0 (μ : Measure Meaning) : Kernel Price Meaning :=
  listener μ (truthful sem)

instance (μ : Measure Meaning) : IsFiniteKernel (L0 μ) :=
  inferInstanceAs (IsFiniteKernel (listener _ (truthful _)))

/-- The cost `C(u)` of eq. 7 is one at a round price and the fitted parameter `c` at a sharp
one. -/
def cost (c : ℝ) (u : Price) : ℝ := if u.IsRound then 1 else c

/-- The goal-indexed speaker, eqs. 5 to 8, knows the answer to her goal and is informative about
the literal listener's distribution over the topical subspace (eq. 6), at unit rationality, less
the cost. -/
noncomputable def S1 (μ : Measure Meaning) (c : ℝ) (p : Meaning × Goal) : Measure Price :=
  speaker 1 (cost c) ((L0 μ).map (project p.2)) Measure.dirac (project p.2 p.1)

instance (μ : Measure Meaning) (c : ℝ) (p : Meaning × Goal) : IsFiniteMeasure (S1 μ c p) :=
  inferInstanceAs (IsFiniteMeasure (speaker _ _ _ _ _))

/-- The pragmatic listener over meaning and goal, eq. 10, inverts the speaker against the product
of the meaning prior and the goal prior; its first marginal is the meaning listener. -/
noncomputable def L1 (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure Goal)
    [IsProbabilityMeasure ν] (c : ℝ) : Kernel Price (Meaning × Goal) :=
  listener (μ.prod ν) (S1 μ c)

section Support

variable (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure Goal)
  [IsProbabilityMeasure ν] (c : ℝ)

/-- A meaning is in the support of the meaning listener at an utterance exactly when it has positive
prior and, under some goal of positive prior, shares its answer with a meaning of positive prior
at which the utterance is literally true. -/
theorem listener_ne_zero_iff (u : Price) (m : Meaning) :
    (L1 μ ν c u).fst {m} ≠ 0
      ↔ μ {m} ≠ 0 ∧ ∃ g, ν {g} ≠ 0 ∧ ∃ m', project g m' = project g m ∧ m'.1 = u ∧ μ {m'} ≠ 0 := by
  rw [L1]
  refine (listener_prod_speaker_map_dirac_fst_apply_singleton_ne_zero_iff one_pos (cost c) (L0 μ)
    project μ ν u m).trans ?_
  simp only [L0, listener_truthful_apply_singleton_ne_zero_iff]
  rfl

/-- A low price with affect is a possible meaning of a high price under the affect goal whenever the
prior gives mass to both meanings with affect, which is hyperbole. -/
theorem hyperbole (hν : ν {(.exact, .affect)} ≠ 0) (h50 : μ {(.p50, true)} ≠ 0)
    (h10k : μ {(.p10000, true)} ≠ 0) : (L1 μ ν c .p10000).fst {(.p50, true)} ≠ 0 := by
  rw [listener_ne_zero_iff μ ν c]
  exact ⟨h50, (.exact, .affect), hν, (.p10000, true), rfl, rfl, h10k⟩

/-- A listener entertaining only the exact price goal, the first comparison model of Fig. 2B,
interprets every utterance literally. -/
theorem literal_of_price_goals (hν : ∀ g, ν {g} ≠ 0 → g = (.exact, .price)) {u : Price}
    {m : Meaning} (h : (L1 μ ν c u).fst {m} ≠ 0) : m.1 = u := by
  obtain ⟨-, g, hg, m', hm', hu', -⟩ := (listener_ne_zero_iff μ ν c u m).mp h
  obtain rfl := hν g hg
  subst hu'
  have : m'.1 = m.1 := by simpa [project, Price.project] using hm'
  exact this.symm

/-- A listener entertaining the price goals, exact or approximate, the second comparison model
of Fig. 2B, reaches only the prices rounding to the utterance. -/
theorem halo_of_price_goals (hν : ∀ g, ν {g} ≠ 0 → g.2 = .price) {u : Price}
    {m : Meaning} (h : (L1 μ ν c u).fst {m} ≠ 0) : m.1.round = u.round := by
  obtain ⟨-, ⟨f, r⟩, hg, m', hm', hu', -⟩ := (listener_ne_zero_iff μ ν c u m).mp h
  obtain rfl : r = .price := hν _ hg
  subst hu'
  cases f
  · have : m'.1 = m.1 := by simpa [project, Price.project] using hm'
    rw [this]
  · have : m'.1.round = m.1.round := by simpa [project, Price.project] using hm'
    rw [this]

end Support

section Halo

variable (μ : Measure Meaning) [IsProbabilityMeasure μ] (c : ℝ)

theorem map_L0_approximate {u p : Price} (hμ : μ (sem u) ≠ 0) (hp : u.round = p.round)
    (a : Bool) : (L0 μ).map (project (.approximate, .price)) u
      {project (.approximate, .price) (p, a)} = 1 := by
  rw [L0, listener_truthful_map_apply_singleton,
    Set.inter_eq_self_of_subset_left (fun m hm ↦ by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, project, Price.project, mem_sem.mp hm, hp]
      rfl),
    ENNReal.div_self hμ (measure_ne_top _ _)]

/-- At an approximate price goal, the speaker prefers the round utterance for a sharp price iff
sharp numbers cost more (Fig. 3B). -/
theorem approximate_prefers_round {p : Price} (hp : ¬ p.IsRound) (h₁ : μ (sem p) ≠ 0)
    (h₂ : μ (sem p.round) ≠ 0) (a : Bool) :
    (S1 μ c ((p, a), (.approximate, .price))).real {p}
        < (S1 μ c ((p, a), (.approximate, .price))).real {p.round} ↔ 1 < c := by
  rw [S1, speaker_dirac_real_singleton_lt_iff zero_le_one
    ⟨p, by rw [map_L0_approximate μ h₁ rfl]; simp⟩,
    map_L0_approximate μ h₁ rfl, map_L0_approximate μ h₂ (Price.round_round p),
    ENNReal.one_rpow, cost, cost, ite_eq_right hp, ite_eq_left (Price.isRound_round p)]
  simp only [one_mul]
  rw [ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _), Real.exp_lt_exp, neg_lt_neg_iff]

end Halo

end KaoWuEtAl2014
