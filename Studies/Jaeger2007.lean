module

public import Linglib.Data.Examples.Jaeger2007
public import Studies.GoldwaterJohnson2003
public import Linglib.Phonology.OptimalityTheory.PartiallyOrderedConstraints
public import Mathlib.Basic.Sign.Basic

/-!
# Jäger (2007): Maximum Entropy Models and Stochastic Optimality Theory

This file formalizes Jäger's result that Boersma's Gradual Learning Algorithm (GLA) for
Stochastic Optimality Theory is stochastic gradient ascent on the log-likelihood of a maximum
entropy model of the kind Goldwater and Johnson propose. The expected GLA adjustment is the
plasticity times the excess of the expected violations over the observed, which is the gradient
of the log-likelihood once violations are read as non-positive features. Since that
log-likelihood is concave, the maximum entropy learner reaches its global maximum, the guarantee
Stochastic OT lacks. The file also reruns Boersma and Levelt's acquisition simulation over five
syllable-structure constraints.

## Implementation notes

* The maximum entropy probabilities are the `HarmonicGrammar.maxEnt` distributions of each
  input's candidates, as in Goldwater and Johnson's model; the sampled estimate of
  the expected violations is stated over an arbitrary distribution on the candidates.
* Table 1 is the paper's data, in permyriad; the initial ranks, 0 for FAITH and 10 for the
  markedness constraints, the learning rate 0.1 and the trajectory of Figure 1 are reported, not
  derived. The simulation's acquisition order refines the stages' ties by frequency, placing
  CVCC before VCC; the stages alone leave them tied.

## References

* [G. Jäger, *Maximum Entropy Models and Stochastic Optimality Theory* (2007)][jaeger-2007]
* [P. Boersma, *Functional Phonology* (1998)][boersma-1998]
* [S. Goldwater and M. Johnson, *Learning OT Constraint Rankings Using a Maximum Entropy Model*
  (2003)][goldwater-johnson-2003]
-/

@[expose] public section

namespace Jaeger2007

open OptimalityTheory HarmonicGrammar MeasureTheory Finset Real GoldwaterJohnson2003

/-! ### The Gradual Learning Algorithm as Stochastic Gradient Ascent -/

/-- The GLA update of Section 2 on a single rank, which adds the plasticity times the sign of the
excess of the sampled hypothesis's violations over the observation's. -/
noncomputable def glaSign (r η : ℝ) (obs hyp : ℕ) : ℝ :=
  r + η * SignType.sign ((hyp : ℝ) - obs)

/-- The GLA update of a rank on binary constraints, which adds the plasticity times the excess of
the sampled hypothesis's violations over the observation's, raising a constraint that favours the
observation and lowering one that favours the hypothesis. -/
def glaUpdate (r η : ℝ) (obs hyp : ℕ) : ℝ :=
  r + η * ((hyp : ℝ) - obs)

theorem glaSign_eq_glaUpdate (r η : ℝ) {obs hyp : ℕ} (ho : obs ≤ 1) (hh : hyp ≤ 1) :
    glaSign r η obs hyp = glaUpdate r η obs hyp := by
  unfold glaSign glaUpdate
  interval_cases obs <;> interval_cases hyp <;> norm_num [sign_apply]

variable {O : Type*} [Fintype O]

/-- The expected GLA update of a rank is the plasticity times the excess of expected over observed
violations (equation (1)). -/
theorem expected_glaUpdate (p : O → ℝ) (hp : ∑ h, p h = 1) (c : O → ℕ) (o : O) (r η : ℝ) :
    ∑ h, p h * glaUpdate r η (c o) (c h) = r + η * (∑ h, p h * c h - c o) := by
  have key : ∀ h, p h * glaUpdate r η (c o) (c h) = p h * r + η * (p h * c h) - η * (p h * c o) :=
    fun h ↦ by simp only [glaUpdate]; ring
  simp only [key, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, hp]
  ring

/-- The learner is at rest iff expected and observed violations agree (Section 4). -/
theorem expected_glaUpdate_eq_self_iff (p : O → ℝ) (hp : ∑ h, p h = 1) (c : O → ℕ) (o : O)
    (r : ℝ) {η : ℝ} (hη : η ≠ 0) :
    ∑ h, p h * glaUpdate r η (c o) (c h) = r ↔ ∑ h, p h * c h = c o := by
  rw [expected_glaUpdate p hp c o r η]
  constructor
  · intro h
    have h' : η * (∑ h, p h * c h - c o) = 0 := by linarith
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact absurd h0 hη
    · linarith
  · intro h
    rw [h, sub_self, mul_zero, add_zero]

variable {I : Type*} [MeasurableSpace O] [MeasurableSingletonClass O] {n : ℕ}

-- (2)
theorem hasDerivAt_log_maxEnt_update (con : ConstraintSet (I × O) (Fin n)) (w : Fin n → ℝ)
    (j : Fin n) (i : I) (o : O) (t : ℝ) :
    HasDerivAt
      (fun t ↦ log ((maxEnt (con.comap (i, ·)).violations (Function.update w j t)).real {o}))
      ((∫ o', (con.comap (i, ·)).violations o' ∂maxEnt (con.comap (i, ·)).violations
        (Function.update w j t)) j - con j (i, o)) t := by
  have : Nonempty O := ⟨o⟩
  simpa [Function.update_idem] using hasDerivAt_logLikelihood_update
    (con.comap (i, ·)).violations (Function.update w j t) (Measure.dirac o) j

/-- The Stochastic Gradient Ascent step of Section 4 on a single weight, which follows the
gradient (2) with the empirical expectation replaced by the observed feature value and the model's
expectation by the feature value of a sampled hypothesis. -/
def sgaUpdate (r η observed sampled : ℝ) : ℝ :=
  r + η * (observed - sampled)

/-- The GLA update is the Stochastic Gradient Ascent step once violations are read as the
non-positive features of the maximum entropy model (Section 4). -/
theorem gla_eq_sga (r η : ℝ) (obs hyp : ℕ) :
    glaUpdate r η obs hyp = sgaUpdate r η (-obs) (-hyp) := by
  simp only [glaUpdate, sgaUpdate]
  ring

/-! ### The Dutch syllable types of Table 1 -/

/-- A syllable type, given by the numbers of consonants in its onset and its coda, at most two
each. -/
abbrev Syl := Fin 3 × Fin 3

/-- The nine types of Table 1. -/
def cv : Syl := (1, 0)
def cvc : Syl := (1, 1)
def vc : Syl := (0, 1)
def v : Syl := (0, 0)
def cvcc : Syl := (1, 2)
def ccvc : Syl := (2, 1)
def ccv : Syl := (2, 0)
def vcc : Syl := (0, 2)
def ccvcc : Syl := (2, 2)

/-- The row of Table 1 recorded by an example, a syllable type with its frequency in permyriad. -/
def Row.ofDatum (e : Datum) : Option (Syl × ℕ) := do
  let on ← e.nat? "onset"
  let co ← e.nat? "coda"
  let f ← e.nat? "permyriad"
  if h : on < 3 ∧ co < 3 then some ((⟨on, h.1⟩, ⟨co, h.2⟩), f) else none

/-- Table 1. -/
def rows : List (Syl × ℕ) := Examples.all.filterMap Row.ofDatum

/-! ### The constraints of Section 5 -/

/-- *CODA, which penalizes a coda. -/
def starCoda : Constraint (Syl × Syl) := Constraint.binary fun c ↦ 1 ≤ c.2.2

/-- ONSET, which penalizes a vowel-initial syllable. -/
def onset : Constraint (Syl × Syl) := Constraint.binary fun c ↦ c.2.1 = 0

/-- *COMPLEXCODA, which penalizes a complex coda. -/
def starComplexCoda : Constraint (Syl × Syl) := Constraint.binary fun c ↦ c.2.2 = 2

/-- *COMPLEXONSET, which penalizes a complex onset. -/
def starComplexOnset : Constraint (Syl × Syl) := Constraint.binary fun c ↦ c.2.1 = 2

/-- FAITH, which penalizes an output that differs from its input. -/
def faith : Constraint (Syl × Syl) := Constraint.binary fun c ↦ c.1 ≠ c.2

/-- The constraint set, in the order of the converged ranking FAITH ≫ *COMPLEXONSET ≫
*COMPLEXCODA ≫ ONSET ≫ *CODA. -/
def con : ConstraintSet (Syl × Syl) (Fin 5) :=
  ![faith, starComplexOnset, starComplexCoda, onset, starCoda]

/-- The syllabification system offers every syllable type as a candidate output for every
input, under the five constraints. -/
def syllabification : ConstraintSystem Syl Syl (Fin 5) := ⟨fun _ ↦ univ, con⟩

theorem faithful_iff (σ : Ranking (Fin 5) 5) (i : Syl) :
    PicksAt syllabification σ i i ↔ ∀ k, con k (i, i) = 1 → σ.Dominates 0 k := by
  revert σ i; decide +kernel

/-- The syllable types produced faithfully once the markedness constraints in `S` are below
FAITH, namely those violating no other markedness constraint. -/
def produced (S : Finset (Fin 5)) : Finset Syl := univ.filter fun i ↦ ∀ k, con k (i, i) = 1 → k ∈ S

theorem mem_produced_iff (σ : Ranking (Fin 5) 5) (i : Syl) :
    i ∈ produced (univ.filter (σ.Dominates 0)) ↔ PicksAt syllabification σ i i := by
  simp [produced, faithful_iff]

/-- The stages at which FAITH overtakes *CODA, ONSET, *COMPLEXCODA and *COMPLEXONSET in turn
produce the syllable types in the nested order CV; CVC; V, VC; CVCC, VCC; CCV, CCVC, CCVCC. -/
theorem produced_stages :
    produced ∅ = {cv} ∧ produced {4} = {cv, cvc} ∧ produced {4, 3} = {cv, cvc, v, vc} ∧
    produced {4, 3, 2} = {cv, cvc, v, vc, cvcc, vcc} ∧ produced {4, 3, 2, 1} = univ := by
  decide

theorem cv_unmarked : ∀ i : Syl, ∀ k : Fin 5, k ≠ 0 → con k (i, cv) = 0 := by decide

-- (1)
theorem initial_glaUpdate (r η : ℝ) (o : Syl) (k : Fin 5) (hk : k ≠ 0) :
    ∑ h, Pi.single (M := fun _ ↦ ℝ) cv 1 h * glaUpdate r η (con k (o, o)) (con k (o, h)) =
      r - η * con k (o, o) := by
  have h :=
    expected_glaUpdate (Pi.single (M := fun _ ↦ ℝ) cv 1) (by simp) (fun h ↦ con k (o, h)) o r η
  rw [h]
  simp [Pi.single_apply, cv_unmarked o k hk]
  ring

/-- The violation rate of a constraint in the corpus of Table 1, in permyriad. -/
def corpusRate (k : Fin 5) : ℕ := (rows.map fun r ↦ r.2 * con k (r.1, r.1)).sum

/-- FAITH is never violated in the corpus, and the markedness ranks fall fastest for *CODA, then
ONSET, *COMPLEXCODA and *COMPLEXONSET, the order in which FAITH overtakes them (Table 1). -/
theorem corpusRate_order :
    corpusRate 0 = 0 ∧ corpusRate 1 < corpusRate 2 ∧ corpusRate 2 < corpusRate 3 ∧
    corpusRate 3 < corpusRate 4 := by
  decide

end Jaeger2007
