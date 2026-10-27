module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Pragmatics.SocialMeaning.Persona
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.DeriveFintype

/-!
# Henderson and McCready (2024): Signaling without Saying: The Semantics and Pragmatics of Dogwhistles

This file formalizes the identifying dogwhistles of Chapter 4, messages that tell part of an
audience who the speaker is while the rest hears something innocuous. The book loosens Burnett's
social meaning games in two ways. A listener holds, besides a prior over the speaker's personae, a
likelihood of each message given each persona, so the literal listener is Bayes' rule over that
likelihood, the RSA listener of the likelihood taken as a channel, and Burnett's literal listener
is the case of a likelihood that is zero or one. And the speaker's social utility for a message
toward a listener sums, over the personae, the log posterior and the speaker's and the listener's
values of the persona weighted by the posterior; the utility toward a group is the sum over its
members, and the speaker chooses by the softmax of that utility. So a group that prefers a message
to a member makes the speaker favour it, and only the proportions of a group matter.

In the case study Jill Stein chooses between *big pharma*, which savvy listeners tie to the
anti-vaxxer persona and unsavvy ones read as merely anti-corporate, and the disavowal *corporate
scientists*. To pro-vaxxers alone, savvy or not, she disavows; to anti-vaxxers alone she
dogwhistles; a savvy pro-vaxxer weighs more against the dogwhistle than an unsavvy one; and to an
audience of 400 anti-vaxxers, 100 savvy and 4500 unsavvy pro-vaxxers she dogwhistles until 74 more
savvy or 1314 more naive pro-vaxxers join it.

## Implementation notes

* The book's probabilities are integer weights in twentieths, since the literal listener
  normalizes.
* The social utility sums over all personae, mathlib's `Real.log 0 = 0` making the terms off the
  posterior's support vanish. That is the sum the book's printed utilities compute, although its
  table of the personae consistent with *corporate scientists* omits the pro-corporate
  anti-vaxxer, to whom its likelihood gives .1.
* The book conditions the speaker on her persona, but the utility does not depend on it, so
  neither does `S1`; its utility is toward a group, the book's single listener being a group of
  one. Stein values no persona over another, so her values are zero.

## TODO

* The book prints 73 for the anti-vaxxer's utility of *big pharma*, where the model gives 72.05;
  the other five printed utilities agree.
* The parameter exploration of Section 4.3 and the enriching dogwhistles of Chapter 5.

## References

* [henderson-mccready-2024]
* [burnett-2019]
* [henderson-mccready-2018]
-/

@[expose] public section

namespace HendersonMcCready2024

open SocialMeaning MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

/-! ### The model -/

section Model

variable {P M : Type*} [MeasurableSpace P] [MeasurableSpace M]

/-- A listener holds a prior over the speaker's personae, a likelihood of each message given each
persona, and an approval of each persona. -/
structure Listener (P M : Type*) [MeasurableSpace P] [MeasurableSpace M] where
  /-- The prior over the speaker's personae. -/
  prior : Measure P
  /-- The likelihood of each message given each persona. -/
  likelihood : P → Measure M
  /-- How much the listener approves of each persona. -/
  approval : P → ℝ

variable [Countable M] [MeasurableSingletonClass M]

/-- The literal listener is Bayes' rule over the likelihood, the RSA listener who takes the
likelihood for the speaker's channel. -/
noncomputable def Listener.L0 (L : Listener P M) : Kernel M P :=
  listener L.prior L.likelihood

/-- A likelihood that is zero or one, as for a lexicalized social meaning, gives Burnett's literal
listener, who conditions the prior on the personae the message is true of. -/
theorem Listener.L0_eq_listener_truthful (L : Listener P M)
    (h : ∀ p m, L.likelihood p {m} = 0 ∨ L.likelihood p {m} = 1) :
    L.L0 = listener L.prior (truthful fun m ↦ {p | L.likelihood p {m} = 1}) := by
  refine congrArg (Kernel.ofDensity L.prior) (funext₂ fun m p ↦ ?_)
  rw [truthful_apply_singleton]
  rcases h p m with h | h <;> simp [h]

theorem Listener.L0_eq_zero (L : Listener P M) {m : M} (h : ∀ p, L.likelihood p {m} = 0) :
    L.L0 m = 0 := by
  simp [Listener.L0, listener_apply, h, ProbabilityTheory.cond]

variable [Fintype P]

/-- The speaker's social utility of a message toward a listener sums, over the personae, the log
posterior and the speaker's and the listener's values of the persona weighted by the
posterior. -/
noncomputable def socialUtility (νS : P → ℝ) (L : Listener P M) (m : M) : ℝ :=
  ∑ p, (Real.log ((L.L0 m).real {p}) + νS p * (L.L0 m).real {p} +
    L.approval p * (L.L0 m).real {p})

/-- The utility toward a group of listeners is the sum over its members. -/
noncomputable def groupUtility (νS : P → ℝ) (G : Multiset (Listener P M)) (m : M) : ℝ :=
  (G.map (socialUtility νS · m)).sum

theorem groupUtility_nsmul (νS : P → ℝ) (n : ℕ) (G : Multiset (Listener P M)) (m : M) :
    groupUtility νS (n • G) m = n * groupUtility νS G m := by
  rw [groupUtility, groupUtility, Multiset.map_nsmul, Multiset.sum_nsmul, nsmul_eq_mul]

variable [MeasurableSingletonClass P] [Fintype M] {α : ℝ} {νS : P → ℝ}
  {G : Multiset (Listener P M)} {p : P} {m m' : M}

/-- The speaker chooses a message by the softmax of its utility toward the group at
rationality `α`. -/
noncomputable def S1 (α : ℝ) (νS : P → ℝ) (G : Multiset (Listener P M)) : Kernel P M :=
  Kernel.softmax fun _ m ↦ ((α * groupUtility νS G m : ℝ) : EReal)

theorem S1_real_singleton_lt_iff (hα : 0 < α) :
    (S1 α νS G p).real {m} < (S1 α νS G p).real {m'} ↔
      groupUtility νS G m < groupUtility νS G m' := by
  rw [S1, Kernel.softmax_coe_real_singleton_lt_iff (fun _ m ↦ α * groupUtility νS G m),
    mul_lt_mul_iff_right₀ hα]

theorem S1_real_singleton_lt_of_forall (hα : 0 < α) (hG : G ≠ 0)
    (h : ∀ L ∈ G, socialUtility νS L m < socialUtility νS L m') :
    (S1 α νS G p).real {m} < (S1 α νS G p).real {m'} :=
  (S1_real_singleton_lt_iff hα).2 (Multiset.sum_lt_sum_of_nonempty hG h)

theorem S1_nsmul_real_singleton_lt_iff (hα : 0 < α) {n : ℕ} (hn : n ≠ 0) :
    (S1 α νS (n • G) p).real {m} < (S1 α νS (n • G) p).real {m'} ↔
      (S1 α νS G p).real {m} < (S1 α νS G p).real {m'} := by
  rw [S1_real_singleton_lt_iff hα, S1_real_singleton_lt_iff hα, groupUtility_nsmul,
    groupUtility_nsmul, mul_lt_mul_iff_right₀ (by positivity)]

end Model

/-! ### Stein's predicament -/

/-- The two issues of the case study. -/
inductive Issue where
  | vaccines
  | corporations
  deriving DecidableEq

/-- The social properties, a stance on each issue. -/
inductive Trait where
  | proVax
  | antiVax
  | proCorporate
  | antiCorporate
  deriving DecidableEq

instance : Fintype Trait :=
  ⟨{.proVax, .antiVax, .proCorporate, .antiCorporate}, fun t ↦ by cases t <;> simp⟩

/-- The issue a trait is a stance on. -/
def Trait.issue : Trait → Issue
  | .proVax | .antiVax => .vaccines
  | .proCorporate | .antiCorporate => .corporations

/-- A persona takes a stance on each issue. -/
abbrev Persona := SocialMeaning.Persona (dimensionalIncompatibility Trait.issue)

def proVaxProCorp : Persona := ⟨{.proVax, .proCorporate}, by decide +kernel⟩
def proVaxAntiCorp : Persona := ⟨{.proVax, .antiCorporate}, by decide +kernel⟩
def antiVaxProCorp : Persona := ⟨{.antiVax, .proCorporate}, by decide +kernel⟩
def antiVaxAntiCorp : Persona := ⟨{.antiVax, .antiCorporate}, by decide +kernel⟩

theorem personae_eq :
    (Finset.univ : Finset Persona) =
      {proVaxProCorp, proVaxAntiCorp, antiVaxProCorp, antiVaxAntiCorp} := by
  decide +kernel

/-- The dogwhistle and the disavowal. -/
inductive Message where
  | bigPharma
  | corporateScientists
  deriving DecidableEq, Fintype

instance : MeasurableSpace Message := ⊤
instance : MeasurableSingletonClass Message :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- Both messages mark Stein as anti-corporate, *big pharma* as anti-vax and *corporate
scientists* as pro-vax. -/
def field : GroundedField Message (dimensionalIncompatibility Trait.issue) where
  indexes
    | .bigPharma => {.antiVax, .antiCorporate}
    | .corporateScientists => {.proVax, .antiCorporate}
  isIndepSet m := by cases m <;> decide

theorem field_personae_bigPharma :
    field.personae .bigPharma = {proVaxAntiCorp, antiVaxProCorp, antiVaxAntiCorp} := by
  decide +kernel

theorem field_personae_corporateScientists :
    field.personae .corporateScientists = {proVaxProCorp, proVaxAntiCorp, antiVaxAntiCorp} := by
  decide +kernel

/-- Every listener's prior about Stein, in twentieths: probably anti-corporate, pro- or anti-vax
equally, and pro-corporate likelier if anti-vax. -/
def priorWeight (π : Persona) : ℕ :=
  if .antiCorporate ∈ π.1 then 8 else if .antiVax ∈ π.1 then 3 else 1

/-- The likelihood of a message given a persona, in twentieths, for a listener who knows the
anti-vaxxer discourse and for one who does not. *Big pharma* is impossible from a persona it does
not meet; the savvy tie it to the anti-vax anti-corporate persona and the unsavvy read it as
mainly anti-corporate. *Corporate scientists* all but rules out the anti-vaxxer and leans
anti-corporate for everyone. -/
def likelihoodWeight (savvy : Bool) : Message → Persona → ℕ
  | .bigPharma, π =>
    if π ∉ field.personae .bigPharma then 0
    else if savvy then (if .antiVax ∈ π.1 ∧ .antiCorporate ∈ π.1 then 16 else 2)
    else if .proVax ∈ π.1 then 14 else if .antiCorporate ∈ π.1 then 3 else 2
  | .corporateScientists, π =>
    if .antiVax ∈ π.1 then 2 else if .proCorporate ∈ π.1 then 12 else 16

/-- An anti-vaxxer knows the discourse, rewards an anti-vax speaker and punishes a pro-vax one,
and slightly punishes a pro-corporate one. -/
noncomputable def antiVaxxer : Listener Persona Message where
  prior := .ofWeights (priorWeight ·)
  likelihood π := .ofWeights fun m ↦ likelihoodWeight true m π
  approval π := (if .antiVax ∈ π.1 then 100 else -100) + (if .proCorporate ∈ π.1 then -25 else 0)

/-- A savvy pro-vaxxer, the anti-vaxxer's mirror image. -/
noncomputable def savvyProVaxxer : Listener Persona Message where
  prior := .ofWeights (priorWeight ·)
  likelihood π := .ofWeights fun m ↦ likelihoodWeight true m π
  approval π := (if .proVax ∈ π.1 then 100 else -100) + (if .proCorporate ∈ π.1 then -25 else 0)

/-- An unsavvy pro-vaxxer does not know the discourse and, less invested, approves less of a
pro-vax speaker. -/
noncomputable def unsavvyProVaxxer : Listener Persona Message where
  prior := .ofWeights (priorWeight ·)
  likelihood π := .ofWeights fun m ↦ likelihoodWeight false m π
  approval π := (if .proVax ∈ π.1 then 75 else -100) + (if .proCorporate ∈ π.1 then -25 else 0)

/-! ### Stein's choice -/

private theorem L0_real_singleton (L : Listener Persona Message) (s : Bool)
    (hp : L.prior = .ofWeights (priorWeight ·))
    (hl : L.likelihood = fun π ↦ .ofWeights fun m ↦ likelihoodWeight s m π) (m : Message)
    (π : Persona) :
    (L.L0 m).real {π} = (likelihoodWeight s m π * priorWeight π : ℝ) /
      ∑ π', (likelihoodWeight s m π' * priorWeight π' : ℝ) := by
  have : L.L0 = Kernel.ofDensity (Measure.ofWeights (priorWeight ·))
      fun m π ↦ (likelihoodWeight s m π : ℝ≥0∞) := by
    simp [Listener.L0, listener, hp, hl]
  rw [this]
  exact Kernel.ofDensity_natCast_real_singleton priorWeight (likelihoodWeight s) m π

private theorem sum_univ (f : Persona → ℝ) :
    ∑ π, f π = f proVaxProCorp + f proVaxAntiCorp + f antiVaxProCorp + f antiVaxAntiCorp := by
  rw [personae_eq, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

private theorem log_savvy :
    Real.log (531441 / 31250) = Real.log (8 / 75) + Real.log (1 / 25) + Real.log (64 / 75) -
      (Real.log (2 / 27) + Real.log (64 / 81) + Real.log (1 / 27) + Real.log (8 / 81)) := by
  rw [show (531441 / 31250 : ℝ) =
    8 / 75 * (1 / 25) * (64 / 75) / (2 / 27 * (64 / 81) * (1 / 27) * (8 / 81)) by norm_num]
  simp (disch := norm_num) only [Real.log_div, Real.log_mul]

private theorem log_unsavvy :
    Real.log (301327047 / 11453152) = Real.log (56 / 71) + Real.log (3 / 71) + Real.log (12 / 71) -
      (Real.log (2 / 27) + Real.log (64 / 81) + Real.log (1 / 27) + Real.log (8 / 81)) := by
  rw [show (301327047 / 11453152 : ℝ) =
    56 / 71 * (3 / 71) * (12 / 71) / (2 / 27 * (64 / 81) * (1 / 27) * (8 / 81)) by norm_num]
  simp (disch := norm_num) only [Real.log_div, Real.log_mul]

private theorem advantage_antiVaxxer :
    socialUtility 0 antiVaxxer .bigPharma - socialUtility 0 antiVaxxer .corporateScientists =
      Real.log (531441 / 31250) + 12416 / 81 := by
  simp only [socialUtility, L0_real_singleton antiVaxxer true rfl rfl, sum_univ]
  simp +decide only [likelihoodWeight, priorWeight, antiVaxxer, field_personae_bigPharma]
  norm_num
  rw [log_savvy]
  ring

private theorem advantage_savvyProVaxxer :
    socialUtility 0 savvyProVaxxer .bigPharma -
        socialUtility 0 savvyProVaxxer .corporateScientists =
      Real.log (531441 / 31250) - 12128 / 81 := by
  simp only [socialUtility, L0_real_singleton savvyProVaxxer true rfl rfl, sum_univ]
  simp +decide only [likelihoodWeight, priorWeight, savvyProVaxxer, field_personae_bigPharma]
  norm_num
  rw [log_savvy]
  ring

private theorem advantage_unsavvyProVaxxer :
    socialUtility 0 unsavvyProVaxxer .bigPharma -
        socialUtility 0 unsavvyProVaxxer .corporateScientists =
      Real.log (301327047 / 11453152) - 66050 / 5751 := by
  simp only [socialUtility, L0_real_singleton unsavvyProVaxxer false rfl rfl, sum_univ]
  simp +decide only [likelihoodWeight, priorWeight, unsavvyProVaxxer, field_personae_bigPharma]
  norm_num
  rw [log_unsavvy]
  ring

private theorem log_savvy_bounds :
    2.833572 < Real.log (531441 / 31250) ∧ Real.log (531441 / 31250) < 2.833574 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -31441 / 500000) (by norm_num [abs_div]) 5
  rw [show (531441 / 31250 : ℝ) = 2 ^ 4 * (1 - -31441 / 500000) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num [Finset.sum_range_succ, abs_le] at h ⊢
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

private theorem log_unsavvy_bounds :
    3.269930 < Real.log (301327047 / 11453152) ∧ Real.log (301327047 / 11453152) < 3.269932 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 292891 / 11453152) (by norm_num [abs_div]) 5
  rw [show (301327047 / 11453152 : ℝ) = 3 ^ 3 * (1 - 292891 / 11453152) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num [Finset.sum_range_succ, abs_le] at h ⊢
  constructor <;> linarith [Real.log_three_gt_d9, Real.log_three_lt_d9]

variable {α : ℝ} {G : Multiset (Listener Persona Message)} {π : Persona}

/-- To any group of pro-vaxxers, savvy or not, Stein disavows. -/
theorem disavows_to_proVaxxers (hα : 0 < α) (hG : G ≠ 0)
    (h : ∀ L ∈ G, L = savvyProVaxxer ∨ L = unsavvyProVaxxer) :
    (S1 α 0 G π).real {.bigPharma} < (S1 α 0 G π).real {.corporateScientists} := by
  refine S1_real_singleton_lt_of_forall hα hG fun L hL ↦ ?_
  rcases h L hL with rfl | rfl
  · linarith [advantage_savvyProVaxxer, log_savvy_bounds.2]
  · linarith [advantage_unsavvyProVaxxer, log_unsavvy_bounds.2]

/-- To any group of anti-vaxxers Stein dogwhistles. -/
theorem dogwhistles_to_antiVaxxers (hα : 0 < α) (hG : G ≠ 0) (h : ∀ L ∈ G, L = antiVaxxer) :
    (S1 α 0 G π).real {.corporateScientists} < (S1 α 0 G π).real {.bigPharma} :=
  S1_real_singleton_lt_of_forall hα hG fun L hL ↦ by
    obtain rfl := h L hL
    linarith [advantage_antiVaxxer, log_savvy_bounds.1]

theorem disavows_of_savvy_for_unsavvy (hα : 0 < α)
    (h : (S1 α 0 (unsavvyProVaxxer ::ₘ G) π).real {.bigPharma} <
      (S1 α 0 (unsavvyProVaxxer ::ₘ G) π).real {.corporateScientists}) :
    (S1 α 0 (savvyProVaxxer ::ₘ G) π).real {.bigPharma} <
      (S1 α 0 (savvyProVaxxer ::ₘ G) π).real {.corporateScientists} := by
  rw [S1_real_singleton_lt_iff hα] at h ⊢
  simp only [groupUtility, Multiset.map_cons, Multiset.sum_cons] at h ⊢
  linarith [advantage_savvyProVaxxer, advantage_unsavvyProVaxxer, log_savvy_bounds.2,
    log_unsavvy_bounds.1]

/-- The book's audience of about 5000: 400 anti-vaxxers, 100 savvy pro-vaxxers, and the rest
naive. -/
noncomputable def mixedAudience : Multiset (Listener Persona Message) :=
  .replicate 400 antiVaxxer + .replicate 100 savvyProVaxxer + .replicate 4500 unsavvyProVaxxer

/-- Stein dogwhistles to the mixed audience until 74 more savvy pro-vaxxers join it, the book's
"few dozen" (p. 65). -/
theorem dogwhistles_iff_savvy_lt (hα : 0 < α) (n : ℕ) :
    (S1 α 0 (.replicate n savvyProVaxxer + mixedAudience) π).real {.corporateScientists} <
      (S1 α 0 (.replicate n savvyProVaxxer + mixedAudience) π).real {.bigPharma} ↔ n < 74 := by
  rw [S1_real_singleton_lt_iff hα]
  simp only [groupUtility, mixedAudience, Multiset.map_add, Multiset.map_replicate,
    Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_ofNat]
  have hA := advantage_antiVaxxer
  have hS := advantage_savvyProVaxxer
  have hU := advantage_unsavvyProVaxxer
  have hs := log_savvy_bounds
  have hu := log_unsavvy_bounds
  have hc : 0 ≤ socialUtility 0 savvyProVaxxer .corporateScientists -
      socialUtility 0 savvyProVaxxer .bigPharma := by linarith
  constructor
  · intro h
    by_contra hn
    have hn : (74 : ℝ) ≤ n := by exact_mod_cast not_lt.1 hn
    linarith [mul_nonneg (sub_nonneg.2 hn) hc]
  · intro hn
    have hn : (n : ℝ) ≤ 73 := by exact_mod_cast Nat.lt_succ_iff.1 hn
    linarith [mul_nonneg (sub_nonneg.2 hn) hc]

/-- Stein dogwhistles to the mixed audience until 1314 more naive listeners join it, the book's
"thousand more" (p. 65). -/
theorem dogwhistles_iff_naive_lt (hα : 0 < α) (n : ℕ) :
    (S1 α 0 (.replicate n unsavvyProVaxxer + mixedAudience) π).real {.corporateScientists} <
      (S1 α 0 (.replicate n unsavvyProVaxxer + mixedAudience) π).real {.bigPharma} ↔
      n < 1314 := by
  rw [S1_real_singleton_lt_iff hα]
  simp only [groupUtility, mixedAudience, Multiset.map_add, Multiset.map_replicate,
    Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_ofNat]
  have hA := advantage_antiVaxxer
  have hS := advantage_savvyProVaxxer
  have hU := advantage_unsavvyProVaxxer
  have hs := log_savvy_bounds
  have hu := log_unsavvy_bounds
  have hc : 0 ≤ socialUtility 0 unsavvyProVaxxer .corporateScientists -
      socialUtility 0 unsavvyProVaxxer .bigPharma := by linarith
  constructor
  · intro h
    by_contra hn
    have hn : (1314 : ℝ) ≤ n := by exact_mod_cast not_lt.1 hn
    linarith [mul_nonneg (sub_nonneg.2 hn) hc]
  · intro hn
    have hn : (n : ℝ) ≤ 1313 := by exact_mod_cast Nat.lt_succ_iff.1 hn
    linarith [mul_nonneg (sub_nonneg.2 hn) hc]

end HendersonMcCready2024
