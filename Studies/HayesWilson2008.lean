module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Linglib.Phonology.HarmonicGrammar.MaxEnt
public import Linglib.Phonology.Segmental.Defs
public import Linglib.Data.Examples.HayesWilson2008

/-!
# Hayes and Wilson (2008): A Maximum Entropy Model of Phonotactics and Phonotactic Learning

This file formalizes Hayes and Wilson's maximum-entropy model of phonotactics. A constraint is a
sequence of feature matrices, one of which may be complemented, and a grammar assigns each form a
score, a maxent value, and a probability. The weights are learned by maximizing the probability
of the data, whose partial derivatives are differences between expected and observed violation
counts (`hasDerivAt_logLik`), and the weights that maximize it give the distribution of greatest
entropy among those that match the observed violations
(`isGreatest_measureEntropy_of_isMaxOn_logLik`).

The grammar the learner found for English onsets (Table 4) is stated over the paper's feature
chart (Table 3), and every score the paper reports is recomputed from it (`rows_scores`),
including the ten attested onsets the grammar penalizes (`attested_penalized`). The predicted
rating orders forms as the score does (`rating_lt_iff`), so the reported correlation with
Scholes's ratings is a claim about the score alone.

## Implementation notes

Weights are kept in hundredths over `ℕ`, so every score is computed by `decide`; the maxent
value and probability then live over `ℝ`. Scores computed from the two-decimal weights of
Table 4 can differ from the paper's reported values by one hundredth ([ð] 4.53 here against
4.54; [θw] 3.90 against 3.91; [θ] and [θr] 1.84 against 1.85), and `rows_scores` states the
reproduction to within that rounding. Complement matrices are read against the
underspecified chart, so `[^+back]` contains every consonant unspecified for backness, as
#15 requires. The probability (6) over the infinite set of forms is realized over a finite
form space, the subtype of a candidate set for the learned grammar (`onsetProb`); the paper's
finite-state approximation of the expected counts is not modelled. The ratings of Scholes's
experiment appear only as a scattergram (Figure 3), so the correlation of 0.946 and Table 5 stay
in prose.

## TODO

* The constraint search of §4 (accuracy O/E with the upper confidence limit, generality, the
  algorithm (10)) and the Gaussian prior of footnote 4.
* Projections (§6–§7), the Shona and stress simulations, and Wargamay (§8).

## References

* [B. Hayes and C. Wilson, *A Maximum Entropy Model of Phonotactics and Phonotactic Learning*
  (2008)][hayes-wilson-2008]
* [S. Della Pietra, V. J. Della Pietra and J. D. Lafferty, *Inducing Features of Random Fields*
  (1997)][della-pietra-della-pietra-lafferty-1997]
* [R. J. Scholes, *Phonotactic Grammaticality* (1966)][scholes-1966]
* [G. N. Clements and S. J. Keyser, *CV Phonology: A Generative Theory of the Syllable*
  (1983)][clements-keyser-1983]
* [S. Goldwater and M. Johnson, *Learning OT Constraint Rankings Using a Maximum Entropy Model*
  (2003)][goldwater-johnson-2003]
-/

@[expose] public section

namespace HayesWilson2008

open Phonology OptimalityTheory HarmonicGrammar Real

/-! ### The segments of Table 3 -/

/-- `Seg` enumerates the English consonants of Table 3. Segments without an ASCII letter take
    their ARPAbet names, with `ch` for [tʃ], `jh` for [dʒ], `th` for [θ], `sh` for [ʃ], `hh` for
    [h], `dh` for [ð], `zh` for [ʒ], and `ng` for [ŋ]. -/
inductive Seg
  | p | t | ch | k | b | d | jh | g | f | th | s | sh | hh | v | dh | z | zh | m | n | ng | l | r
  | j | w
  deriving DecidableEq, Repr

namespace Seg

/-- The chart of Table 3 lists, for each feature, the segments specified `+` and then those
    specified `−`. A segment in neither list is unspecified for the feature, as in the chart's
    blanks (privative and contrastive underspecification, §4.1.2). -/
def chart : Feature → List Seg × List Seg
  | .consonantal =>
    ([p, t, ch, k, b, d, jh, g, f, th, s, sh, hh, v, dh, z, zh, m, n, ng, l], [r, j, w])
  | .approximant =>
    ([l, r, j, w], [p, t, ch, k, b, d, jh, g, f, th, s, sh, hh, v, dh, z, zh, m, n, ng])
  | .sonorant =>
    ([m, n, ng, l, r, j, w], [p, t, ch, k, b, d, jh, g, f, th, s, sh, hh, v, dh, z, zh])
  | .continuant => ([f, th, s, sh, hh, v, dh, z, zh], [p, t, ch, k, b, d, jh, g])
  | .nasal => ([m, n, ng], [])
  | .voice => ([b, d, jh, g, v, dh, z, zh], [p, t, ch, k, f, th, s, sh, hh])
  | .spreadGlottis => ([hh], [])
  | .labial => ([p, b, f, v, m, w], [])
  | .coronal => ([t, ch, d, jh, th, s, sh, dh, z, zh, n, l, r], [])
  | .anterior => ([t, d, th, s, dh, z, n, l], [ch, jh, sh, zh, r])
  | .strident => ([ch, jh, s, sh, z, zh], [t, d, th, dh, n, l, r])
  | .lateral => ([l], [])
  | .dorsal => ([k, g, ng], [])
  | .high => ([j, w], [])
  | .back => ([w], [j])
  | _ => ([], [])

/-- The feature specification of a segment is read off the chart. -/
def spec (x : Seg) : Segment := fun f ↦
  if x ∈ (chart f).1 then Flat.some true else if x ∈ (chart f).2 then Flat.some false else ⊥

/-- `ofChar` reads the segment written by one IPA letter. -/
def ofChar : Char → Option Seg
  | 'p' => some p | 't' => some t | 'k' => some k | 'b' => some b | 'd' => some d
  | 'g' => some g | 'f' => some f | 'θ' => some th | 's' => some s | 'ʃ' => some sh
  | 'h' => some hh | 'v' => some v | 'ð' => some dh | 'z' => some z | 'ʒ' => some zh
  | 'm' => some m | 'n' => some n | 'ŋ' => some ng | 'l' => some l | 'r' => some r
  | 'j' => some j | 'w' => some w | _ => none

/-- `parse` reads an onset off a row's IPA string, with the affricates written as digraphs. -/
def parse : List Char → Option (List Seg)
  | [] => some []
  | 't' :: 'ʃ' :: cs => (parse cs).map (ch :: ·)
  | 'd' :: 'ʒ' :: cs => (parse cs).map (jh :: ·)
  | c :: cs => (ofChar c).bind fun x ↦ (parse cs).map (x :: ·)

end Seg

/-! ### Constraints (§4.1.1) -/

/-- A matrix of a constraint (9) is a natural class `[αF, βG, …]`, its complement
    `[^αF, βG, …]` (the implication operator), or the word boundary `#`. -/
inductive Matrix
  | cls (pat : Segment)
  | compl (pat : Segment)
  | boundary

variable {α : Type*}

/-- A matrix matches one symbol of a boundary-padded form, read through the segment
    specification `spec`; `none` is a word boundary. -/
def Matrix.Matches (spec : α → Segment) : Matrix → Option α → Prop
  | .cls pat, some x => pat ≤ spec x
  | .compl pat, some x => ¬ pat ≤ spec x
  | .boundary, none => True
  | _, _ => False

instance (spec : α → Segment) : ∀ (m : Matrix) (x : Option α), Decidable (m.Matches spec x)
  | .cls _, some _ => inferInstanceAs (Decidable (_ ≤ _))
  | .compl _, some _ => inferInstanceAs (Decidable (¬ _ ≤ _))
  | .boundary, none => inferInstanceAs (Decidable True)
  | .cls _, none | .compl _, none | .boundary, some _ => inferInstanceAs (Decidable False)

/-- A phonotactic constraint (9) is a sequence of matrices. -/
abbrev Cx := List Matrix

/-- The matrices match the padded form from its first symbol on. -/
def Cx.prefixMatch (spec : α → Segment) : Cx → List (Option α) → Bool
  | [], _ => true
  | m :: ms, x :: xs => decide (m.Matches spec x) && Cx.prefixMatch spec ms xs
  | _ :: _, [] => false

/-- A constraint's violation count on a form is the number of positions of the boundary-padded
    form at which its matrices match, as (9) specifies. -/
def Cx.violations (spec : α → Segment) (c : Cx) (form : List α) : ℕ :=
  ((none :: form.map some ++ [none]).tails.filter (c.prefixMatch spec)).length

/-- `M l` is the natural class `[αF, βG, …]` of the specifications `l`. -/
def M (l : List (Feature × Bool)) : Matrix := .cls (Segment.ofSpecs l)

/-- `M' l` is the complement class `[^αF, βG, …]` of the specifications `l`. -/
def M' (l : List (Feature × Bool)) : Matrix := .compl (Segment.ofSpecs l)

/-- The empty matrix `[ ]` matches any segment. -/
def any : Matrix := .cls (Segment.ofSpecs [])

/-! ### Score, maxent value, and probability (§3.2) -/

/-- The score (4) of a form is its weighted violation count, with weights in hundredths. -/
def score {n : ℕ} (spec : α → Segment) (con : Fin n → Cx) (w : Fin n → ℕ)
    (form : List α) : ℕ :=
  w ⬝ᵥ fun j ↦ (con j).violations spec form

/-- The maxent value (5) of a form whose score in hundredths is `k` is `exp (−h(x))`. -/
noncomputable def maxentValue (k : ℕ) : ℝ := exp (-(k : ℝ) / 100)

theorem maxentValue_pos (k : ℕ) : 0 < maxentValue k := exp_pos _

theorem maxentValue_lt_iff {k₁ k₂ : ℕ} :
    maxentValue k₁ < maxentValue k₂ ↔ k₂ < k₁ := by
  rw [maxentValue, maxentValue, exp_lt_exp, div_lt_div_iff_of_pos_right (by norm_num),
    neg_lt_neg_iff, Nat.cast_lt]

theorem maxentValue_zero : maxentValue 0 = 1 := by simp [maxentValue]

/-- The predicted rating (12) is the maxent value raised to `1 / T` for a temperature `T`. -/
noncomputable def rating (T : ℝ) (k : ℕ) : ℝ := maxentValue k ^ (1 / T)

theorem rating_lt_iff {T : ℝ} (hT : 0 < T) {k₁ k₂ : ℕ} :
    rating T k₁ < rating T k₂ ↔ k₂ < k₁ := by
  rw [rating, rating, rpow_lt_rpow_iff (maxentValue_pos _).le (maxentValue_pos _).le
    (one_div_pos.2 hT), maxentValue_lt_iff]

/-- Table 1 evaluates schematic forms over consonants `C` and vowels `V` with two constraints,
    `*#V` weighted 3.0 and `*C#` weighted 2.0. -/
inductive CV
  | C
  | V
  deriving DecidableEq, Repr

/-- `C` is `[−syllabic]`, `V` is `[+syllabic]` (footnote 7). -/
def CV.spec : CV → Segment
  | .C => Segment.ofSpecs [(.syllabic, false)]
  | .V => Segment.ofSpecs [(.syllabic, true)]

/-- Table 1 has the constraints `*#V` and `*C#`. -/
def table1 : Fin 2 → Cx :=
  ![[.boundary, M [(.syllabic, true)]], [M [(.syllabic, false)], .boundary]]

/-- The weights of Table 1 are written in hundredths. -/
def table1W : Fin 2 → ℕ := ![300, 200]

-- Table 1
theorem table1_scores :
    score CV.spec table1 table1W [.C, .V] = 0 ∧
      score CV.spec table1 table1W [.C, .V, .C] = 200 ∧
        score CV.spec table1 table1W [.V] = 300 := by decide

-- Table 1
theorem table1_maxentValues :
    maxentValue (score CV.spec table1 table1W [.C, .V]) = 1 ∧
      maxentValue (score CV.spec table1 table1W [.C, .V, .C]) = exp (-2) ∧
        maxentValue (score CV.spec table1 table1W [.V]) = exp (-3) := by
  obtain ⟨h₁, h₂, h₃⟩ := table1_scores
  rw [h₁, h₂, h₃]
  norm_num [maxentValue]

/-! ### Learning the weights (§3.3) -/

section Learning

open MeasureTheory InformationTheory
open scoped ENNReal

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] {n : ℕ} (viol : ConstraintSet Ω (Fin n))
  (w : Fin n → ℝ) (D : Ω → ℕ)

/-- The observed number of violations of constraint `i` sums its counts over data given as
    counts per form. -/
def observed (i : Fin n) : ℕ :=
  ∑ x, D x * viol i x

/-- The log probability of the data (7) sums the log probabilities (6) of the forms, each
    weighted by its count, since the forms are independent. -/
noncomputable def logLik : ℝ :=
  ∑ x, D x * log ((maxEnt viol.violations w).real {x})

/-- The empirical distribution of data given as counts per form. -/
noncomputable def empirical : Measure Ω :=
  ∑ x, ((D x : ℝ≥0∞) / ∑ y, (D y : ℝ≥0∞)) • Measure.dirac x

theorem isProbabilityMeasure_empirical (hD : ∑ x, D x ≠ 0) :
    IsProbabilityMeasure (empirical D) := by
  constructor
  have hN : (∑ y, (D y : ℝ≥0∞)) ≠ 0 := by exact_mod_cast hD
  simp only [empirical, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, div_eq_mul_inv, ← Finset.sum_mul]
  exact ENNReal.mul_inv_cancel hN (ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.natCast_ne_top _)

variable [MeasurableSingletonClass Ω]

theorem empirical_real_singleton (x : Ω) :
    (empirical D).real {x} = D x / ∑ y, (D y : ℝ) := by
  classical
  simp only [empirical, measureReal_def, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single x (fun y _ hy ↦ by simp [hy]) (by simp)]
  simp [ENNReal.toReal_div, ENNReal.toReal_sum fun _ _ ↦ ENNReal.natCast_ne_top _]

theorem logLik_eq (hD : ∑ x, D x ≠ 0) :
    logLik viol w D = (∑ x, D x : ℕ) * logLikelihood viol.violations (empirical D) w := by
  have := isProbabilityMeasure_empirical D hD
  have hN : (∑ x, D x : ℝ) ≠ 0 := by exact_mod_cast hD
  simp only [logLik, logLikelihood, integral_fintype .of_finite, empirical_real_singleton,
    smul_eq_mul, Finset.mul_sum, Nat.cast_sum]
  exact Finset.sum_congr rfl fun x _ ↦ by field_simp

theorem integral_violations_empirical (hD : ∑ x, D x ≠ 0) (i : Fin n) :
    (∫ x, viol.violations x ∂empirical D) i = observed viol D i / ∑ x, (D x : ℝ) := by
  have := isProbabilityMeasure_empirical D hD
  simp only [integral_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    empirical_real_singleton, ConstraintSet.violations_apply, observed, Nat.cast_sum,
    Nat.cast_mul, Finset.sum_div]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

variable [Nonempty Ω]

/-- The partial derivative of the log likelihood in a constraint weight is the scaled expected count
(8) minus the observed count ([della-pietra-della-pietra-lafferty-1997], §3.3.2). -/
theorem hasDerivAt_logLik (i : Fin n) :
    HasDerivAt (fun t ↦ logLik viol (Function.update w i t) D)
      ((∑ x, D x : ℕ) * (∫ x, viol.violations x ∂maxEnt viol.violations w) i -
        observed viol D i) (w i) := by
  have h (x : Ω) :
      HasDerivAt (fun t ↦ log ((maxEnt viol.violations (Function.update w i t)).real {x}))
        ((∫ x, viol.violations x ∂maxEnt viol.violations w) i - viol i x) (w i) := by
    simpa only [logLikelihood_dirac, integral_dirac, ConstraintSet.violations_apply] using
      hasDerivAt_logLikelihood_update viol.violations w (Measure.dirac x) i
  unfold logLik
  refine (HasDerivAt.fun_sum fun x (_ : x ∈ Finset.univ) ↦
    (h x).const_mul (D x : ℝ)).congr_deriv ?_
  simp only [observed, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, mul_sub,
    Finset.sum_sub_distrib]

/-- Weights maximizing the data's probability give the maximum-entropy distribution among those
matching the observed violations (§3.3.1, [della-pietra-della-pietra-lafferty-1997]). -/
theorem isGreatest_measureEntropy_of_isMaxOn_logLik (hD : ∑ x, D x ≠ 0)
    (h : IsMaxOn (fun w ↦ logLik viol w D) Set.univ w) :
    IsGreatest (measureEntropy '' {q : Measure Ω | IsProbabilityMeasure q ∧
      ∫ x, (viol.violations x : Fin n → ℝ) ∂q = ∫ x, viol.violations x ∂empirical D})
        (Hm[maxEnt viol.violations w]) := by
  have := isProbabilityMeasure_empirical D hD
  have hN : (0 : ℝ) < (∑ x, D x : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hD
  refine isGreatest_measureEntropy_of_isMaxOn viol.violations w (empirical D)
    (isMaxOn_iff.2 fun w' _ ↦ ?_)
  have hw' : logLik viol w' D ≤ logLik viol w D := h (Set.mem_univ w')
  rw [logLik_eq viol _ D hD, logLik_eq viol _ D hD] at hw'
  exact le_of_mul_le_mul_left hw' hN

end Learning

/-! ### The learned grammar for English onsets (Table 4) -/

/-- Table 4 lists 23 constraints in the order they were learned. -/
def table4 : Fin 23 → Cx := ![
  [M [(.sonorant, true), (.dorsal, true)]],
  [M [(.continuant, true), (.voice, true), (.anterior, false)]],
  [M' [(.voice, false), (.anterior, true), (.strident, true)], M [(.approximant, false)]],
  [any, M [(.continuant, true)]],
  [any, M [(.voice, true)]],
  [M [(.sonorant, true)], any],
  [M [(.strident, false)], M [(.consonantal, true)]],
  [any, M [(.strident, true)]],
  [M [(.labial, true)], M' [(.approximant, true), (.coronal, true)]],
  [M [(.anterior, false)], M' [(.approximant, true), (.anterior, false)]],
  [M [(.continuant, true), (.voice, true)], any],
  [M [(.continuant, false), (.anterior, false)], any],
  [any, M [(.back, false)]],
  [M [(.anterior, true), (.strident, true)], M [(.anterior, false)]],
  [M [(.spreadGlottis, true)], M' [(.back, true)]],
  [M [(.continuant, true), (.voice, true), (.coronal, true)]],
  [M [(.voice, true)], M' [(.approximant, true), (.coronal, true)]],
  [M [(.continuant, true), (.strident, false)], M' [(.approximant, true), (.anterior, false)]],
  [any, M' [(.continuant, false), (.voice, false), (.labial, true)], M [(.consonantal, true)]],
  [any, M [(.coronal, true)], M' [(.approximant, true), (.anterior, false)]],
  [M [(.continuant, true), (.strident, false)]],
  [M [(.strident, true)], M [(.anterior, false)]],
  [M [(.continuant, false), (.voice, false), (.coronal, true)],
    M' [(.approximant, true), (.anterior, false)]]]

/-- The weights of Table 4 are written in hundredths. -/
def table4W : Fin 23 → ℕ :=
  ![564, 328, 591, 517, 537, 666, 440, 131, 496, 484, 484, 317, 504, 280, 482, 269, 297, 206,
    305, 206, 184, 210, 170]

open Seg

/-- `h o` is the score (4) of the onset `o` under the learned grammar, in hundredths. -/
def h (o : List Seg) : ℕ := score Seg.spec table4 table4W o

/-- `viol k o` counts the violations of constraint `k + 1` of Table 4 on the onset `o`. -/
def viol (k : Fin 23) (o : List Seg) : ℕ := (table4 k).violations Seg.spec o

/-- The learning data (11) are the onsets of the nonexotic corpus, read off the rows. -/
def attested : List (List Seg) :=
  Examples.all.filterMap fun e ↦
    if e.feature? "corpus" = some "(11)" then Seg.parse e.primaryText.toList else none

-- §5.3.1
theorem attested_le : ∀ o ∈ attested, h o ≤ 453 := by decide

/-- Exactly ten attested onsets, the rarest ones, receive penalties ((11), §5.3.1). -/
theorem attested_penalized :
    (attested.filter (h · ≠ 0)).map (fun o ↦ (o, h o)) =
      [([th], 184), ([z], 269), ([th, r], 184), ([t, w], 170), ([sh, r], 210), ([dh], 453),
        ([d, w], 297), ([g, w], 297), ([th, w], 390), ([s, k, l], 305)] := by decide

/-- These are the twelve unattested onsets with the best scores (§5.3.1). -/
def twelve : List (List Seg) :=
  [[s, t, w], [d, l], [hh, l], [hh, r], [v, l], [v, r], [sh, l], [sh, w], [s, r], [f, w], [p, w],
    [s, p, w]]

-- §5.3.1
theorem twelve_scores :
    twelve.map h = [376, 440, 482, 482, 484, 484, 484, 484, 490, 496, 496, 496] := by decide

theorem h_rt : h [r, t] = 2181 ∧ viol 2 [r, t] = 1 ∧ viol 5 [r, t] = 1 ∧ viol 6 [r, t] = 1 ∧
    viol 9 [r, t] = 1 := by decide

-- §5.2
theorem stch_gang :
    h [s, ch] = 621 ∧ viol 7 [s, ch] = 1 ∧ viol 13 [s, ch] = 1 ∧ viol 21 [s, ch] = 1 ∧
      table4W 7 < 400 ∧ table4W 13 < 400 ∧ table4W 21 < 400 := by decide

theorem zh_gang : h [zh] = 597 ∧ viol 1 [zh] = 1 ∧ viol 15 [zh] = 1 := by decide

theorem thw_gang : h [th, w] = 390 ∧ viol 17 [th, w] = 1 ∧ viol 20 [th, w] = 1 := by decide

/-- `digits cs` reads a decimal numeral. -/
def digits (cs : List Char) : Option ℕ :=
  if cs ≠ [] ∧ cs.all Char.isDigit then
    some (cs.foldl (fun n c ↦ 10 * n + (c.toNat - '0'.toNat)) 0)
  else none

/-- `hundredths s` reads a reported two-decimal score in hundredths. -/
def hundredths (s : String) : Option ℕ :=
  match s.toList.span (· ≠ '.') with
  | (whole, '.' :: frac) => (digits whole).bind fun x ↦ (digits frac).map fun y ↦ 100 * x + y
  | _ => none

/-- A row that reports a score is reproduced when its onset parses and the grammar's score is
    within one hundredth of the reported one. -/
def Reproduced (e : Datum) : Prop :=
  ∀ sc ∈ e.feature? "score", ∃ o ∈ Seg.parse e.primaryText.toList, ∃ k ∈ hundredths sc,
    ((h o : ℤ) - k).natAbs ≤ 1

instance : DecidablePred Reproduced := fun e ↦ by unfold Reproduced; infer_instance

/-- Every score the paper reports (§5.2–5.3) is reproduced by the grammar to within one
    hundredth, the rounding of the printed weights. -/
theorem rows_scores : ∀ e ∈ Examples.all, Reproduced e := by decide +kernel

/-! ### Probability over a candidate set (§3.2, (6)) -/

/-- The candidate set contains the attested onsets and the unattested ones discussed. -/
def candidates : Finset (List Seg) :=
  (attested ++ twelve ++ [[r, t], [s, ch], [zh]]).toFinset

instance : Nonempty candidates := ⟨⟨[r, t], by decide +kernel⟩⟩

instance : MeasurableSpace candidates := ⊤
instance : MeasurableSingletonClass candidates := ⟨fun _ ↦ trivial⟩

/-- The constraints of Table 4 on the candidate set. -/
def onsetCon : ConstraintSet candidates (Fin 23) := fun k o ↦ viol k o

/-- `onsetProb` is the probability (6) of each candidate under the learned grammar, with the
    weights of Table 4 read as reals. -/
noncomputable def onsetProb (o : candidates) : ℝ :=
  (maxEnt onsetCon.violations fun k ↦ (table4W k : ℝ) / 100).real {o}

-- (6), (4)
theorem onsetProb_eq_softmax : onsetProb = softmax fun o : candidates ↦ -(h o : ℝ) / 100 := by
  funext o
  rw [onsetProb, maxEnt_real_singleton, harmony_violations]
  congr 1
  funext o
  rw [harmonyScore_eq_neg_sum]
  simp only [onsetCon, h, score, dotProduct, viol, Nat.cast_sum, Nat.cast_mul, neg_div,
    Finset.sum_div]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ ↦ by ring)

-- (6)
theorem onsetProb_lt_iff {o₁ o₂ : candidates} : onsetProb o₁ < onsetProb o₂ ↔ h o₂ < h o₁ := by
  rw [onsetProb_eq_softmax, softmax_lt_softmax_iff, div_lt_div_iff_of_pos_right (by norm_num),
    neg_lt_neg_iff, Nat.cast_lt]

theorem onsetProb_rt_lt_stw :
    onsetProb ⟨[r, t], by decide +kernel⟩ < onsetProb ⟨[s, t, w], by decide +kernel⟩ :=
  onsetProb_lt_iff.2 (by decide +kernel)

end HayesWilson2008
