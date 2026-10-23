module

public import Linglib.Data.Experiments.ClausWalch2024
public import Linglib.Fragments.English.NumeralModifiers
public import Linglib.Fragments.German.NumeralModifiers
public import Studies.Blok2015
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.NormNum

/-!
# Claus and Walch (2024): Numeral Modification and Framing Effects: exactly and at most vs up to

A framing effect is a difference in choices between two descriptions of one outcome, one in
terms of a goal-consistent count (lives saved) and one in terms of the rest (lives lost). Claus
and Walch find, in German, that the effect survives *genau* 'exactly', and that it is standard
under *bis zu* 'up to' but reversed under *höchstens* 'at most', in risky-choice and attribute
framing alike. They argue that neither finding fits an account on which a frame matters only
through the outcomes its reading leaves open, and propose that a choice follows the valence of
the partial outcome a description makes salient, with *at most* but not *up to* making the
complement set salient, following Blok.

## Main statements

* `outcomes_positive_eq_negative_iff`: the two frames leave open the same outcomes just in case
  the numeral is read precisely, the premise of the arithmetic argument for their equivalence.
* `no_reading_only_account`: no account that sees a modifier only through its truth-conditional
  readings predicts the opposite effects of *bis zu* and *höchstens*.
* `salienceEffect_eq_framingEffect`: the salience and valence account predicts the direction
  of the framing effect in all six conditions.

## Implementation notes

* The German modifiers are the German Fragment's entries, and for salience *bis zu* and
  *höchstens* raise what Blok gives *up to* and *at most*; the paper calls them equivalents and
  reports Blok's contrast for German.
* A description makes the complement set salient when what it asserts is compatible with no
  instance of the predicate, which is Blok's *if any* diagnostic. Blok's *up to* asserts only a
  lower bound, on her scale of the whole numbers; with the upper bound of its Fragment reading
  *bis zu* would pattern with *höchstens* (`salience_raised_bisZu`).
* The complement of a partial outcome has the opposite valence, as lives lost are to lives saved.
* A framing effect is the sign of the difference of the printed percentages; the significance
  tests are stored in the data module and not re-checked here.

## References

* [B. Claus and M. C. Walch, *Numeral Modification and Framing Effects: exactly and at most vs
  up to* (2024)][claus-walch-2024]
* [D. Blok, *The semantics and pragmatics of directional numeral modifiers* (2015)][blok-2015]
* [D. R. Mandel, *Do framing effects reveal irrational choice?* (2014)][mandel-2014]
-/

@[expose] public section

namespace ClausWalch2024

open Data.Experiments Degree Semantics English.NumeralModifiers German.NumeralModifiers Set

variable {N p q n : ℕ}

/-! ### The scenarios -/

/-- The deadly-disease problem of risky-choice framing (Experiments 1 and 2) and the
financial-allocation problem of attribute framing (Experiments 1 and 3). -/
inductive Scenario where
  | deadlyDisease | financialAllocation
  deriving DecidableEq, Fintype

namespace Scenario

/-- The individuals at stake, lives or projects. -/
def total : Scenario → ℕ
  | deadlyDisease => livesAtStake
  | financialAllocation => projects

/-- The number the sure option names in a frame. -/
def number : Scenario → Frame → ℕ
  | deadlyDisease, .positive => livesSaved
  | deadlyDisease, .negative => livesLost
  | financialAllocation, .positive => successfulProjects
  | financialAllocation, .negative => unsuccessfulProjects

theorem number_add (s : Scenario) : s.number .positive + s.number .negative = s.total := by
  cases s <;> rfl

/-- The percentages of Tables 1–2, under *genau*. -/
def genau : Scenario → Frame → Decimal
  | deadlyDisease, f => (table1 f).percent
  | financialAllocation, f => (table2 f).percent

/-- The percentages of Tables 3–4, under *bis zu* and *höchstens*. -/
def upper : Scenario → Modifier → Frame → Decimal
  | deadlyDisease, m, f => (table3 m f).percent
  | financialAllocation, m, f => (table4 m f).percent

end Scenario

/-! ### The outcomes a frame leaves open -/

/-- The goal-consistent counts out of `N` that the sure option leaves open under a reading `m`, a
modifier of sets of amounts: the positive frame says `m {p}` of them, the negative frame `m {q}`
of the rest. -/
def outcomes (m : _root_.Modifier (Set ℕ)) (N p q : ℕ) : Frame → Set ℕ
  | .positive => {k | k ≤ N ∧ k ∈ m {p}}
  | .negative => {k | k ≤ N ∧ N - k ∈ m {q}}

theorem outcomes_negative (c : Comparison) (h : p + q = N) :
    outcomes c.modifier N p q .negative = outcomes c.dual.modifier N p q .positive := by
  ext k
  cases c <;> simp [outcomes] <;> omega

/-- The arithmetic argument for the equivalence of the frames presupposes a precise reading
(p. 4145): the frames leave open the same outcomes just in case the numeral is read precisely. -/
theorem outcomes_positive_eq_negative_iff (c : Comparison) (h : p + q = N) (hp : 0 < p) :
    outcomes c.modifier N p q .positive = outcomes c.modifier N p q .negative ↔ c = .eq := by
  rw [outcomes_negative c h]
  refine ⟨fun he ↦ ?_, fun hc ↦ hc ▸ rfl⟩
  have h0 := congrArg (0 ∈ ·) he
  cases c <;> simp [outcomes] at h0 ⊢ <;> omega

/-! ### The range account

On [mandel-2014]'s account the frames differ under a lower-bound reading because the positive
one leaves open more lives saved (p. 4145); the paper extends the reasoning to an upper-bound
reading, which should reverse the effect (p. 4147). -/

/-- On the range account the frame whose outcomes reach higher draws more choices, so its
framing effect is the sign of the most goal-consistent outcomes the positive frame leaves open
less the most the negative frame does. -/
noncomputable def rangeEffect (m : _root_.Modifier (Set ℕ)) (N p q : ℕ) : SignType :=
  SignType.sign
    ((sSup (outcomes m N p q .positive) : ℕ) - (sSup (outcomes m N p q .negative) : ℕ) : ℤ)

theorem rangeEffect_eq (h : p + q = N) : rangeEffect Comparison.eq.modifier N p q = 0 := by
  rw [rangeEffect, outcomes_negative _ h, Comparison.dual_eq, sub_self, sign_zero]

theorem rangeEffect_ge (h : p + q = N) (hq : 0 < q) :
    rangeEffect Comparison.ge.modifier N p q = 1 := by
  have hpos : outcomes Comparison.ge.modifier N p q .positive = Icc p N := by
    ext k; simp [outcomes, and_comm]
  have hneg : outcomes Comparison.ge.modifier N p q .negative = Iic p := by
    ext k; simp [outcomes]; omega
  rw [rangeEffect, hpos, hneg, (isGreatest_Icc (by omega)).csSup_eq, isGreatest_Iic.csSup_eq]
  exact sign_pos (by omega)

theorem rangeEffect_dual (c : Comparison) (h : p + q = N) :
    rangeEffect c.dual.modifier N p q = -rangeEffect c.modifier N p q := by
  rw [rangeEffect, rangeEffect, outcomes_negative c.dual h, Comparison.dual_dual,
    ← outcomes_negative c h, ← Left.sign_neg, neg_sub]

theorem rangeEffect_le (h : p + q = N) (hq : 0 < q) :
    rangeEffect Comparison.le.modifier N p q = -1 := by
  rw [← Comparison.dual_ge, rangeEffect_dual _ h, rangeEffect_ge h hq]

/-! ### The observed framing effects -/

/-- The framing effect in a condition is the sign of the positive frame's percentage of
sure-option choices or approvals less the negative frame's. -/
def framingEffect (percent : Frame → Decimal) : SignType :=
  SignType.sign ((percent .positive).toRat - (percent .negative).toRat)

theorem framingEffect_genau (s : Scenario) : framingEffect s.genau = 1 := by
  cases s <;> norm_num [framingEffect, Scenario.genau, table1, table2, Decimal.toRat]

theorem framingEffect_bisZu (s : Scenario) : framingEffect (s.upper .bisZu) = 1 := by
  cases s <;> norm_num [framingEffect, Scenario.upper, table3, table4, Decimal.toRat]

theorem framingEffect_hoechstens (s : Scenario) : framingEffect (s.upper .hoechstens) = -1 := by
  cases s <;> norm_num [framingEffect, Scenario.upper, table3, table4, Decimal.toRat]

/-! ### Readings alone -/

/-- The Fragment entry of a modifier. -/
def Modifier.entry : Modifier → Numerals.NumeralModifier
  | .bisZu => German.NumeralModifiers.bisZu
  | .hoechstens => German.NumeralModifiers.hoechstens

/-- *Bis zu* and *höchstens* have the same readings and opposite framing effects in either
scenario (the significant interactions, p. 4148), so no account that sees a modifier only
through its readings predicts both. -/
theorem no_reading_only_account (P : Set (_root_.Modifier (Set ℕ)) → SignType) (s : Scenario) :
    ¬ (P ⟦Modifier.bisZu.entry⟧ = framingEffect (s.upper .bisZu) ∧
      P ⟦Modifier.hoechstens.entry⟧ = framingEffect (s.upper .hoechstens)) := by
  rintro ⟨h₁, h₂⟩
  have := h₁.symm.trans h₂
  rw [framingEffect_bisZu, framingEffect_hoechstens] at this
  exact absurd this (by decide)

/-- At the experiments' numbers the range account predicts no effect under *genau*, against the
significant effects of Experiment 1 (p. 4147), and a reversed one under both upper bounds, right
for *höchstens* and wrong for *bis zu*. -/
theorem rangeEffect_fragment (s : Scenario) :
    (∀ m ∈ ⟦genau⟧,
      rangeEffect m s.total (s.number .positive) (s.number .negative) ≠ framingEffect s.genau) ∧
    (∀ m ∈ ⟦Modifier.bisZu.entry⟧, rangeEffect m s.total (s.number .positive)
      (s.number .negative) ≠ framingEffect (s.upper .bisZu)) ∧
    ∀ m ∈ ⟦Modifier.hoechstens.entry⟧, rangeEffect m s.total (s.number .positive)
      (s.number .negative) = framingEffect (s.upper .hoechstens) := by
  have hq : 0 < s.number .negative := by cases s <;> decide
  refine ⟨?_, ?_, ?_⟩ <;> rintro m (rfl : m = _) <;>
    simp [rangeEffect_eq s.number_add, rangeEffect_le s.number_add hq, framingEffect_genau,
      framingEffect_bisZu, framingEffect_hoechstens]

/-! ### Salience and valence -/

/-- The valence of the partial outcome a frame names, as goal consistency (p. 4149). -/
def Frame.valence : Frame → SignType
  | .positive => 1
  | .negative => -1

open Classical in
/-- A description raising the possibilities `P` makes the complement set salient (`-1`) when
what it asserts is compatible with no instance of the predicate at all, and otherwise the
instances (`1`). -/
noncomputable def salience (P : Set (Set ℕ)) : SignType :=
  if 0 ∈ ⋃₀ P then -1 else 1

/-- The valence of the partial outcome a frame makes salient, when the sure option names
`number f` with a modifier raising `raise n` with the number `n`, is the frame's valence,
reversed when the complement set is salient. -/
noncomputable def appraisal (raise : ℕ → Set (Set ℕ)) (number : Frame → ℕ) (f : Frame) :
    SignType :=
  f.valence * salience (raise (number f))

/-- On the salience and valence account the choice follows the appraisal of the salient partial
outcome, so its framing effect is the sign of the difference of the two frames' appraisals. -/
noncomputable def salienceEffect (raise : ℕ → Set (Set ℕ)) (number : Frame → ℕ) : SignType :=
  SignType.sign ((appraisal raise number .positive : ℤ) - appraisal raise number .negative)

/-- The possibilities a modifier raises with the number `n`, one for each of its readings in the
Fragment. -/
def raised (w : Numerals.NumeralModifier) (n : ℕ) : Set (Set ℕ) := (· {n}) '' ⟦w⟧

/-- The possibilities *bis zu* and *höchstens* raise, by [blok-2015]. -/
def Modifier.raise : Modifier → ℕ → Set (Set ℕ)
  | .bisZu => Blok2015.upTo 1
  | .hoechstens => Blok2015.atMost

theorem salience_raised_genau (hn : 0 < n) : salience (raised genau n) = 1 := by
  simp [salience, raised, genau]; omega

theorem salience_bisZu (hn : 1 ≤ n) : salience (Modifier.bisZu.raise n) = 1 := by
  simp [salience, Modifier.raise, Blok2015.sUnion_upTo hn]

theorem salience_hoechstens : salience (Modifier.hoechstens.raise n) = -1 := by
  simp [salience, Modifier.raise, Blok2015.sUnion_atMost]

theorem salienceEffect_eq_framingEffect (s : Scenario) :
    salienceEffect (raised genau) s.number = framingEffect s.genau ∧
      ∀ m, salienceEffect m.raise s.number = framingEffect (s.upper m) := by
  have hp : 1 ≤ s.number .positive := by cases s <;> decide
  have hq : 1 ≤ s.number .negative := by cases s <;> decide
  refine ⟨?_, fun m ↦ ?_⟩
  · simp [salienceEffect, appraisal, salience_raised_genau hp, salience_raised_genau hq,
      framingEffect_genau, Frame.valence]
  · cases m <;> simp [salienceEffect, appraisal, salience_bisZu hp, salience_bisZu hq,
      salience_hoechstens, framingEffect_bisZu, framingEffect_hoechstens, Frame.valence]

/-- On the Fragment's readings the classification reproduces the paper's lists (p. 4149), with
*more than*, *at least* and *exactly* making the instances salient and *fewer than* and *at most*
the complement set. -/
theorem salience_raised (hn : 0 < n) :
    (∀ w ∈ [moreThan, atLeast, exactly], salience (raised w n) = 1) ∧
    ∀ w ∈ [fewerThan, atMost], salience (raised w n) = -1 := by
  constructor <;> intro w hw <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hw <;>
    rcases hw with rfl | rfl | rfl <;>
      simp [salience, raised, moreThan, atLeast, exactly, fewerThan, atMost] <;> omega

theorem salience_raised_bisZu : salience (raised bisZu n) = -1 := by
  simp [salience, raised, German.NumeralModifiers.bisZu]

end ClausWalch2024
