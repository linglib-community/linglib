module

public import Linglib.Core.Algebra.Order.Interval.Set.Instances
public import Linglib.Data.Experiments.TonhauserBeaverDegen2018
public import Linglib.Semantics.Presupposition.Trigger
public import Mathlib.Tactic.Linarith

/-!
# Tonhauser, Beaver and Degen (2018): How Projective Is Projective Content? Gradience in Projectivity and At-Issueness

Tonhauser, Beaver and Degen's Gradient Projection Principle says that content embedded under an
entailment-cancelling operator projects to the extent that it is not at-issue. Projectivity and
at-issueness are gradient, measured on the unit interval, so the principle is the involution
`Set.Icc.symm` (`gppProjection`); restricted to binary at-issueness it is the Projection Principle
of Simons, Tonhauser, Beaver and Roberts, that content projects iff it is not at-issue
(`gppProjection_eq_one_iff`). The categorical analyses the paper reviews predict projection at
the ceiling (`ceilingProjection`).

Against the observed means of `Data.Experiments.TonhauserBeaverDegen2018`, the principle is the
closer account on every content but the pre-state of *stop* (`gpp_closer_than_ceiling`,
`ceiling_closer_on_stop`), the effect it predicts holds in all four experiments
(`atIssuenessEffect_beta_pos`), and the printed Tukey comparisons divide the contents into more
than two projectivity classes, cutting across the hard/soft classification (`three_classes`,
`soft_not_a_class`, `hard_soft_indistinguishable`).

## Implementation notes

* Degrees are `Set.Icc (0 : ℚ) 1`: the observations are printed decimals, read through
  `Decimal.toRat`, and every comparison is exact ℚ arithmetic closed by `decide +kernel`.
* The paper's own test of the principle is the sign and size of the at-issueness effect in
  its regressions, kept as data in `atIssuenessEffect`; the error comparison against the
  ceiling is the paper's review of categorical analyses at the granularity this file can
  check. No theorem re-thresholds a printed p-value.
* `Distinguished` reads the paper's printed Tukey verdicts; what counts as distinguished is
  the paper's mark, not a recomputed test. The paper leaves open whether at-issueness causes
  projection.

## References

* [tonhauser-beaver-degen-2018]
* [simons-tonhauser-beaver-roberts-2010]
* [beaver-roberts-simons-tonhauser-2017]
* [karttunen-1973]
* [gazdar-1979]
* [heim-1983]
* [van-der-sandt-1992]
* [potts-2005]
-/

@[expose] public section

namespace TonhauserBeaverDegen2018

open Data.Experiments Set.Icc

/-! ### The Gradient Projection Principle -/

/-- By (7), content projects to the extent that it is not at-issue. -/
def gppProjection : Set.Icc (0 : ℚ) 1 → Set.Icc (0 : ℚ) 1 := Set.Icc.symm

theorem gppProjection_antitone : Antitone gppProjection := antitone_symm

theorem gppProjection_lt_iff {a b : Set.Icc (0 : ℚ) 1} :
    gppProjection a < gppProjection b ↔ b < a :=
  symm_lt_symm

theorem gppProjection_eq_one_iff {ai : Set.Icc (0 : ℚ) 1} : gppProjection ai = 1 ↔ ai = 0 :=
  symm_eq_one

theorem gppProjection_eq_zero_iff {ai : Set.Icc (0 : ℚ) 1} : gppProjection ai = 0 ↔ ai = 1 :=
  symm_eq_zero

/-! ### Projection at the ceiling -/

/-- Projection at the ceiling whatever the at-issueness: what [karttunen-1973], [gazdar-1979]
and global accommodation predict for a presupposition not under a plug or a filter, and
[potts-2005] for a conventional implicature. -/
def ceilingProjection (_ : Set.Icc (0 : ℚ) 1) : Set.Icc (0 : ℚ) 1 := 1

@[simp] theorem ceilingProjection_val (ai : Set.Icc (0 : ℚ) 1) :
    (ceilingProjection ai).val = 1 := rfl

theorem gppProjection_eq_ceiling_iff {ai : Set.Icc (0 : ℚ) 1} :
    gppProjection ai = ceilingProjection ai ↔ ai = 0 :=
  symm_eq_one

/-! ### The observed degrees

The by-expression means are rationals in the unit interval, lifted to `Set.Icc (0 : ℚ) 1`
once and for all. -/

theorem heterogeneous_mem (e : Expression) :
    (heterogeneous e).projectivity.toRat ∈ Set.Icc (0 : ℚ) 1 ∧
      (heterogeneous e).notAtIssueness.toRat ∈ Set.Icc (0 : ℚ) 1 := by
  revert e; decide +kernel

theorem predicates_mem (p : Predicate) :
    (predicates p).projectivity.toRat ∈ Set.Icc (0 : ℚ) 1 ∧
      (predicates p).notAtIssueness.toRat ∈ Set.Icc (0 : ℚ) 1 := by
  revert p; decide +kernel

/-- The observed projectivity of a heterogeneous expression's content, Experiment 1a. -/
def Expression.projectivity (e : Expression) : Set.Icc (0 : ℚ) 1 :=
  ⟨_, (heterogeneous_mem e).1⟩

/-- Its observed not-at-issueness. -/
def Expression.notAtIssueness (e : Expression) : Set.Icc (0 : ℚ) 1 :=
  ⟨_, (heterogeneous_mem e).2⟩

/-- Its observed at-issueness: the released data code the asking-whether response so that `1`
is not-at-issue. -/
def Expression.atIssueness (e : Expression) : Set.Icc (0 : ℚ) 1 :=
  Set.Icc.symm e.notAtIssueness

/-- The observed projectivity of a predicate's complement, Experiment 1b. -/
def Predicate.projectivity (p : Predicate) : Set.Icc (0 : ℚ) 1 := ⟨_, (predicates_mem p).1⟩

/-- Its observed not-at-issueness. -/
def Predicate.notAtIssueness (p : Predicate) : Set.Icc (0 : ℚ) 1 := ⟨_, (predicates_mem p).2⟩

/-- Its observed at-issueness. -/
def Predicate.atIssueness (p : Predicate) : Set.Icc (0 : ℚ) 1 :=
  Set.Icc.symm p.notAtIssueness

theorem gppProjection_atIssueness (e : Expression) :
    gppProjection e.atIssueness = e.notAtIssueness :=
  symm_symm _

/-! ### Errors on the observations -/

/-- The absolute error of an account on content observed at at-issueness `a` and
projectivity `p`. -/
def error (f : Set.Icc (0 : ℚ) 1 → Set.Icc (0 : ℚ) 1) (a p : Set.Icc (0 : ℚ) 1) : ℚ :=
  |(f a : ℚ) - p|

theorem gpp_closer_iff (a p : Set.Icc (0 : ℚ) 1) :
    error gppProjection a p < error ceilingProjection a p ↔
      (Set.Icc.symm a : ℚ) < 1 ∧ 2 * (p : ℚ) < 1 + Set.Icc.symm a := by
  simp only [error, gppProjection, ceilingProjection, Set.Icc.coe_one]
  have hp := p.2.2
  have ha := (Set.Icc.symm a).2.2
  rcases le_or_gt (p : ℚ) (Set.Icc.symm a) with h | h
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact ⟨fun h' => ⟨by linarith, by linarith⟩, fun h' => by linarith [h'.1]⟩
  · rw [abs_of_neg (by linarith), abs_of_nonneg (by linarith)]
    exact ⟨fun h' => ⟨by linarith, by linarith⟩, fun h' => by linarith [h'.2]⟩

theorem nrrc_more_projective_than_discover :
    Expression.nrrc.atIssueness < Expression.discover.atIssueness ∧
      gppProjection Expression.discover.atIssueness <
        gppProjection Expression.nrrc.atIssueness ∧
      Expression.discover.projectivity < Expression.nrrc.projectivity := by
  decide +kernel

theorem gpp_closer_than_ceiling (e : Expression) (h : e ≠ .stop) :
    error gppProjection e.atIssueness e.projectivity <
      error ceilingProjection e.atIssueness e.projectivity := by
  revert e; decide +kernel

theorem ceiling_closer_on_stop :
    error ceilingProjection Expression.stop.atIssueness Expression.stop.projectivity <
      error gppProjection Expression.stop.atIssueness Expression.stop.projectivity := by
  decide +kernel

/-- The unrestricted universal is false. -/
example : ¬ ∀ e : Expression,
    error gppProjection e.atIssueness e.projectivity <
      error ceilingProjection e.atIssueness e.projectivity := by
  decide +kernel

theorem gpp_closer_than_ceiling_predicates (p : Predicate) :
    error gppProjection p.atIssueness p.projectivity <
      error ceilingProjection p.atIssueness p.projectivity := by
  revert p; decide +kernel

theorem atIssuenessEffect_beta_pos (x : Experiment) : 0 < (atIssuenessEffect x).beta.toRat := by
  revert x; decide +kernel

/-! ### Projectivity classes from the printed comparisons -/

/-- Two Experiment 1a contents' projectivity means are distinguished by the printed Tukey
comparison. -/
def Expression.Distinguished (a b : Expression) : Prop :=
  ∃ r ∈ pairwise1a, ((r.first = a ∧ r.second = b) ∨ (r.first = b ∧ r.second = a)) ∧
    r.significance ≠ .ns ∧ r.significance ≠ .marginal

instance : DecidableRel Expression.Distinguished :=
  fun _ _ => inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Two Experiment 1b complements' projectivity means are distinguished. -/
def Predicate.Distinguished (a b : Predicate) : Prop :=
  ∃ r ∈ pairwise1b, ((r.first = a ∧ r.second = b) ∨ (r.first = b ∧ r.second = a)) ∧
    r.significance ≠ .ns ∧ r.significance ≠ .marginal

instance : DecidableRel Predicate.Distinguished :=
  fun _ _ => inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem three_classes :
    Expression.Distinguished .nrrc .stop ∧ Expression.Distinguished .stop .only ∧
      Expression.Distinguished .nrrc .only := by
  decide +kernel

/-- `Distinguished` rejects a pair the table marks `n.s`. -/
example : ¬ Expression.Distinguished .nrrc .know := by decide +kernel

theorem know_indistinguishable_from_annoyed : ¬ Expression.Distinguished .know .annoyed := by
  decide +kernel

/-- The hard/soft classification the paper checks its ranking against, as it cites it for the
Experiment 1a contents: *be annoyed* is a hard trigger, and *discover*, *stop* and *only* are soft
triggers. -/
def Expression.hardness? : Expression → Option Presupposition.Hardness
  | .annoyed => some .hard
  | .discover | .stop | .only => some .soft
  | _ => none

theorem some_differences_align :
    Expression.Distinguished .discover .annoyed ∧ Expression.Distinguished .stop .annoyed := by
  decide +kernel

theorem soft_not_a_class :
    ∃ a b, a.hardness? = some .soft ∧ b.hardness? = some .soft ∧
      Expression.Distinguished a b :=
  ⟨.stop, .only, rfl, rfl, by decide +kernel⟩

theorem hard_soft_indistinguishable :
    ∀ h ∈ [Predicate.annoyed, .amused],
      ∀ s ∈ [Predicate.notice, .aware, .realize, .see, .findOut, .learn],
        ¬ h.Distinguished s := by
  decide +kernel

theorem establish_least_projective (p : Predicate) (h : p ≠ .establish) :
    Predicate.Distinguished .establish p := by
  revert p; decide +kernel

end TonhauserBeaverDegen2018
