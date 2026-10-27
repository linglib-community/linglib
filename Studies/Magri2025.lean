module

public import Studies.ZurawHayes2017

/-!
# Magri (2025): Constraint Interaction in Probabilistic Phonology

Hayes and Zuraw observed that the rates of a variable process on four forms crossing two
independent factors lie on two sigmoids shifted against each other at shared abscissas, which is
to say that their logits differ by a constant along each factor (§2.2,
`exists_shiftedSigmoids_iff`). Magri asks which modes of constraint interaction predict this. In
harmony-based probabilistic phonology a form's candidates have probabilities proportional to a
positive harmony of their violation profiles (23) (`grammar`), and the answer is a
characterization (§5.5): the grammar predicts the generalization (24) iff its harmony is
separable, a product of powers of positive unary functions each fed the violations of a single
constraint (30) (`predictsHZ_iff_separable`). Equivalently the harmony of any profile is the
product of the harmonies of its single-constraint profiles (32).

The maximum entropy grammar (14) is the MaxEnt distribution of the form's candidates
(`grammar_meHarmony`), and any separable grammar is the maximum entropy grammar of the
constraints rescaled by `Ĉₖ = −log hₖ(Cₖ)` (33), whose violations are no longer integers (35)
(`grammar_prod_rpow`). Feeding the weighted violations to the inverse function instead of the
exponential (27) is not separable: on the Tagalog square, whose rows and columns are independent
relative to six of Zuraw and Hayes's constraints (§2.3), it satisfies the constant difference only
when the two prefix constraints have equal weights or the two stem-nasal constraints have none
(§4.4, `inverseHarmony_hz_tagalog_iff`).

## Implementation notes

* A harmony is a function `(Fin n → ℕ) → ℝ` of violation profiles, positive and normalized as
  §4.1 assumes; decreasingness is not needed. `PredictsHZ` is (24) for forms with the two
  candidates YES and NO, read as `true` and `false`. Its log-odds form holds exactly for any
  number of candidates (`Separable.interaction_logOdds_eq_zero`), where §3.5 states the logits
  only approximately.
* The converse direction takes one square per constraint. Letting constraint `k` vary along the
  rows and the others along the columns gives
  `H (update u k c) = H (single k c) * H (update u k 0)`, whence (32) by induction on the
  constraints.
* The Tagalog square crosses the prefix constructions *maŋ-* OTHER and *maŋ-* RED-, which the
  paper calls *maŋ-* and *paŋ-* (footnote 1), with the stems /b/ and /k/. Its constraints are
  Zuraw and Hayes's less *[root m/n/ŋ, which penalizes every substitution (footnote 3).
* The weights of (30) add no generality to the class of separable harmonies, since `hₖ ^ wₖ` is
  itself a unary function (`separable_iff_exists_prod`); they matter to the grammars a learner
  can reach, not to the characterization.

## References

* [magri-2025]
* [zuraw-hayes-2017]
* [hayes-2022]
-/

@[expose] public section

namespace Magri2025

open Real OptimalityTheory HarmonicGrammar Function Finset MeasureTheory ZurawHayes2017

variable {n : ℕ} {H : (Fin n → ℕ) → ℝ}

/-! ### Shifted sigmoids (§2.1–2.2) -/

/-- Four rates lie on two sigmoids at shared abscissas, shifted by `δ`, exactly when their logit
differences along the rows agree ((7), (9), §2.2). -/
theorem exists_shiftedSigmoids_iff {X : Type*} (sq : Square X) {r : X → ℝ}
    (hr : ∀ x, r x ∈ Set.Ioo 0 1) :
    (∃ x₁ x₂ δ : ℝ, r sq.tl = sigmoid x₁ ∧ r sq.tr = sigmoid x₂ ∧ r sq.bl = sigmoid (x₁ + δ) ∧
      r sq.br = sigmoid (x₂ + δ)) ↔ sq.interaction (fun x ↦ logit (r x)) = 0 := by
  constructor
  · rintro ⟨x₁, x₂, δ, h₁, h₂, h₃, h₄⟩
    simp only [Square.interaction_apply, h₁, h₂, h₃, h₄, logit_sigmoid]
    ring
  · intro h
    rw [Square.interaction_apply] at h
    refine ⟨logit (r sq.tl), logit (r sq.tr), logit (r sq.bl) - logit (r sq.tl), ?_, ?_, ?_, ?_⟩
    · rw [sigmoid_logit (hr _)]
    · rw [sigmoid_logit (hr _)]
    · rw [add_sub_cancel, sigmoid_logit (hr _)]
    · rw [show logit (r sq.tr) + (logit (r sq.bl) - logit (r sq.tl)) = logit (r sq.br) by linarith,
        sigmoid_logit (hr _)]

/-! ### Harmony-based grammars (§4) -/

/-- The log-odds of candidate `a` against `b` for form `x` under harmony `H`, the log of the
ratio of their harmonies, which is the log of the ratio of their probabilities
(`log_grammar_div`). -/
noncomputable def logOdds {X Y : Type*} (H : (Fin n → ℕ) → ℝ) (con : ConstraintSet (X × Y) (Fin n))
    (a b : Y) (x : X) : ℝ :=
  log (H (con · (x, a)) / H (con · (x, b)))

section Grammar

variable {X Y : Type*} [MeasurableSpace Y]

/-- The harmony-based grammar (23) realizes form `x` as candidate `y` with probability
proportional to the harmony of the violation profile of `(x, y)`. -/
noncomputable def grammar (H : (Fin n → ℕ) → ℝ) (con : ConstraintSet (X × Y) (Fin n)) (x : X) :
    Measure Y :=
  Measure.count.tilted fun y ↦ log (H (con · (x, y)))

variable [Fintype Y] [MeasurableSingletonClass Y]

theorem grammar_real_singleton (hpos : ∀ v, 0 < H v) (con : ConstraintSet (X × Y) (Fin n))
    (x : X) (y : Y) :
    (grammar H con x).real {y} = H (con · (x, y)) / ∑ z, H (con · (x, z)) := by
  simp [grammar, tilted_real_singleton, exp_log (hpos _)]

theorem log_grammar_div (hpos : ∀ v, 0 < H v) (con : ConstraintSet (X × Y) (Fin n)) (x : X)
    (a b : Y) :
    log ((grammar H con x).real {a} / (grammar H con x).real {b}) = logOdds H con a b x := by
  rw [grammar_real_singleton hpos, grammar_real_singleton hpos,
    div_div_div_cancel_right₀ (sum_pos (fun z _ ↦ hpos _) ⟨a, mem_univ a⟩).ne', logOdds]

-- (17)
theorem logit_grammar_of_pair [DecidableEq Y] (hpos : ∀ v, 0 < H v)
    (con : ConstraintSet (X × Y) (Fin n)) (x : X) {a b : Y} (hab : a ≠ b)
    (huniv : (univ : Finset Y) = {a, b}) :
    logit ((grammar H con x).real {a}) = logOdds H con a b x := by
  rw [logit, ← log_grammar_div hpos con x a b]
  congr 2
  rw [grammar_real_singleton hpos, grammar_real_singleton hpos, huniv, sum_pair hab]
  have ha := hpos (con · (x, a))
  have hb := hpos (con · (x, b))
  field_simp
  ring

end Grammar

/-- A harmony predicts HZ's generalization (24) when, on every square of forms with the two
candidates YES and NO whose rows and columns are independent relative to the constraints, the
logits of YES differ by the same amount along both rows. -/
def PredictsHZ (H : (Fin n → ℕ) → ℝ) : Prop :=
  ∀ (X : Type) (sq : Square X) (con : ConstraintSet (X × Bool) (Fin n)), sq.Independent con →
    sq.interaction (fun x ↦ logit ((grammar H con x).real {true})) = 0

/-- A harmony is separable (30) when it is a product of powers of positive unary functions, each
fed the violations of a single constraint. -/
def Separable (H : (Fin n → ℕ) → ℝ) : Prop :=
  ∃ (h : Fin n → ℕ → ℝ) (w : Fin n → ℝ), (∀ k c, 0 < h k c) ∧ ∀ v, H v = ∏ k, h k (v k) ^ w k

/-- The weights of (30) add no generality, since a separable harmony is a product of positive
unary functions. -/
theorem separable_iff_exists_prod :
    Separable H ↔ ∃ g : Fin n → ℕ → ℝ, (∀ k c, 0 < g k c) ∧ ∀ v, H v = ∏ k, g k (v k) :=
  ⟨fun ⟨h, w, hh, hH⟩ ↦ ⟨fun k c ↦ h k c ^ w k, fun k c ↦ rpow_pos_of_pos (hh k c) _, hH⟩,
    fun ⟨g, hg, hH⟩ ↦ ⟨g, 1, hg, by simpa using hH⟩⟩

theorem Separable.pos (hH : Separable H) (v : Fin n → ℕ) : 0 < H v := by
  obtain ⟨g, hg, hH⟩ := separable_iff_exists_prod.1 hH
  rw [hH]
  exact prod_pos fun k _ ↦ hg k _

/-! ### Separable harmonies predict the generalization (§5.4) -/

theorem Separable.interaction_logOdds_eq_zero (hH : Separable H) {X Y : Type*} {sq : Square X}
    {con : ConstraintSet (X × Y) (Fin n)} (hind : sq.Independent con) (a b : Y) :
    sq.interaction (logOdds H con a b) = 0 := by
  obtain ⟨g, hg, hgH⟩ := separable_iff_exists_prod.1 hH
  convert hind.interaction_sum_eq_zero fun k v ↦ log (g k (v a)) - log (g k (v b)) using 2
  ext x
  rw [logOdds, log_div (hH.pos _).ne' (hH.pos _).ne', hgH, hgH,
    log_prod fun k _ ↦ (hg k _).ne', log_prod fun k _ ↦ (hg k _).ne', ← sum_sub_distrib]
  rfl

-- §5.4
theorem Separable.predictsHZ (hH : Separable H) : PredictsHZ H := by
  intro X sq con hind
  simp_rw [logit_grammar_of_pair hH.pos con _ (a := true) (b := false) (by decide) (by decide)]
  exact hH.interaction_logOdds_eq_zero hind true false

/-! ### Only separable harmonies predict the generalization (§5.5) -/

/-- The constraints of the converse's square. Constraint `k` is violated `c` times by candidate
`true` of the top row, and every other constraint `j` is violated `u j` times by candidate `true`
of the left column. -/
private def witness (u : Fin n → ℕ) (k : Fin n) (c : ℕ) : ConstraintSet ((Bool × Bool) × Bool)
    (Fin n) :=
  fun j p ↦ if p.2 then if j = k then (if p.1.1 then c else 0) else (if p.1.2 then u j else 0)
    else 0

private def witnessSquare : Square (Bool × Bool) :=
  ⟨(true, true), (true, false), (false, true), (false, false)⟩

private theorem witnessSquare_independent (u : Fin n → ℕ) (k : Fin n) (c : ℕ) :
    witnessSquare.Independent (witness u k c) := by
  intro j
  by_cases hj : j = k
  · exact .inr ⟨funext fun y ↦ by simp [witness, witnessSquare, hj],
      funext fun y ↦ by simp [witness, witnessSquare, hj]⟩
  · exact .inl ⟨funext fun y ↦ by simp [witness, witnessSquare, hj],
      funext fun y ↦ by simp [witness, witnessSquare, hj]⟩

theorem PredictsHZ.mul_update (hH : PredictsHZ H) (hpos : ∀ v, 0 < H v) (h0 : H 0 = 1)
    (u : Fin n → ℕ) (k : Fin n) (c : ℕ) :
    H (update u k c) = H (Pi.single k c) * H (update u k 0) := by
  have row (p : Bool × Bool) : (witness u k c · (p, false)) = 0 := by ext; simp [witness]
  have tl : (witness u k c · (witnessSquare.tl, true)) = update u k c := by
    ext j; by_cases hj : j = k <;> simp [witness, witnessSquare, hj]
  have tr : (witness u k c · (witnessSquare.tr, true)) = Pi.single k c := by
    ext j; by_cases hj : j = k <;> simp [witness, witnessSquare, hj]
  have bl : (witness u k c · (witnessSquare.bl, true)) = update u k 0 := by
    ext j; by_cases hj : j = k <;> simp [witness, witnessSquare, hj]
  have br : (witness u k c · (witnessSquare.br, true)) = 0 := by ext; simp [witness, witnessSquare]
  have := hH _ _ _ (witnessSquare_independent u k c)
  simp_rw [logit_grammar_of_pair hpos _ _ (a := true) (b := false) (by decide) (by decide)] at this
  simp only [Square.interaction_apply, logOdds, row, tl, tr, bl, br, h0, div_one, log_one] at this
  refine log_injOn_pos (hpos _) (mul_pos (hpos _) (hpos _)) ?_
  rw [log_mul (hpos _).ne' (hpos _).ne']
  linarith

-- (32)
theorem PredictsHZ.eq_prod_single (hH : PredictsHZ H) (hpos : ∀ v, 0 < H v) (h0 : H 0 = 1)
    (v : Fin n → ℕ) : H v = ∏ k, H (Pi.single k (v k)) := by
  classical
  suffices ∀ s : Finset (Fin n), H (s.piecewise v 0) = ∏ k ∈ s, H (Pi.single k (v k)) by
    simpa using this univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert k s hk ih =>
    rw [prod_insert hk, ← ih, piecewise_insert, hH.mul_update hpos h0,
      update_eq_self_iff.2 (by simp [hk] : (0 : ℕ) = s.piecewise v 0 k)]

/-- The characterization of §5.5. A positive normalized harmony predicts HZ's generalization iff
it is separable. -/
theorem predictsHZ_iff_separable (hpos : ∀ v, 0 < H v) (h0 : H 0 = 1) :
    PredictsHZ H ↔ Separable H :=
  ⟨fun h ↦ separable_iff_exists_prod.2 ⟨fun k c ↦ H (Pi.single k c), fun _ _ ↦ hpos _,
    h.eq_prod_single hpos h0⟩, Separable.predictsHZ⟩

-- (30), (32)
theorem separable_iff_eq_prod_single (hpos : ∀ v, 0 < H v) (h0 : H 0 = 1) :
    Separable H ↔ ∀ v, H v = ∏ k, H (Pi.single k (v k)) :=
  ⟨fun h ↦ ((predictsHZ_iff_separable hpos h0).2 h).eq_prod_single hpos h0,
    fun h ↦ separable_iff_exists_prod.2 ⟨fun k c ↦ H (Pi.single k c), fun _ _ ↦ hpos _, h⟩⟩

/-! ### Maximum entropy harmony (§3, §5.1) -/

/-- Maximum entropy harmony (14b) of a real-valued violation profile. -/
noncomputable def meHarmony (w r : Fin n → ℝ) : ℝ :=
  exp (-∑ k, w k * r k)

/-- The maximum entropy grammar (14) is the MaxEnt distribution of the form's candidates. -/
theorem grammar_meHarmony {X Y : Type*} [Fintype Y] [MeasurableSpace Y]
    (w : Fin n → ℝ) (con : ConstraintSet (X × Y) (Fin n)) (x : X) :
    grammar (fun v ↦ meHarmony w fun k ↦ v k) con x = maxEnt (con.comap (x, ·)).violations w := by
  simp only [grammar, maxEnt, meHarmony, log_exp]
  congr 1

-- (29)
theorem separable_meHarmony (w : Fin n → ℝ) : Separable fun v ↦ meHarmony w fun k ↦ v k :=
  ⟨fun _ c ↦ exp (-c), w, fun _ _ ↦ exp_pos _, fun v ↦ by
    simp only [meHarmony, ← exp_mul, ← exp_sum, ← sum_neg_distrib, mul_neg, mul_comm]⟩

-- §3.6
theorem predictsHZ_meHarmony (w : Fin n → ℝ) : PredictsHZ fun v ↦ meHarmony w fun k ↦ v k :=
  (separable_meHarmony w).predictsHZ

/-! ### Constraint rescaling (§5.3) -/

/-- The rescaled constraint (33), `Ĉₖ = −log hₖ(Cₖ)`. -/
noncomputable def rescale (h : Fin n → ℕ → ℝ) (k : Fin n) (c : ℕ) : ℝ :=
  -log (h k c)

-- (34)
theorem prod_rpow_eq_meHarmony_rescale {h : Fin n → ℕ → ℝ} (hpos : ∀ k c, 0 < h k c)
    (w : Fin n → ℝ) (v : Fin n → ℕ) :
    ∏ k, h k (v k) ^ w k = meHarmony w fun k ↦ rescale h k (v k) := by
  simp only [meHarmony, rescale, mul_neg, sum_neg_distrib, neg_neg, exp_sum,
    rpow_def_of_pos (hpos _ _), mul_comm]

/-- Any separable grammar is the maximum entropy grammar of the rescaled constraints (35), whose
violations need not be integers. -/
theorem grammar_prod_rpow {X Y : Type*} [Fintype Y] [MeasurableSpace Y] {h : Fin n → ℕ → ℝ}
    (hpos : ∀ k c, 0 < h k c) (w : Fin n → ℝ) (con : ConstraintSet (X × Y) (Fin n)) (x : X) :
    grammar (fun v ↦ ∏ k, h k (v k) ^ w k) con x =
      maxEnt (fun y k ↦ rescale h k (con k (x, y))) w := by
  simp only [grammar, maxEnt, prod_rpow_eq_meHarmony_rescale hpos, meHarmony, log_exp]
  congr 1

variable {h : Fin n → ℕ → ℝ} {k : Fin n}

-- footnote 14
theorem strictMono_rescale (hpos : ∀ c, 0 < h k c) (hanti : StrictAnti (h k)) :
    StrictMono (rescale h k) :=
  fun _ _ hab ↦ neg_lt_neg (log_lt_log (hpos _) (hanti hab))

-- footnote 15
theorem rescale_eq_zero_iff (hpos : ∀ c, 0 < h k c) (hanti : StrictAnti (h k)) (h0 : h k 0 = 1)
    {c : ℕ} : rescale h k c = 0 ↔ c = 0 := by
  rw [← (strictMono_rescale hpos hanti).injective.eq_iff, rescale, rescale, h0]
  simp

-- footnote 16
theorem rescale_nonneg (hpos : ∀ c, 0 < h k c) (hanti : StrictAnti (h k)) (h0 : h k 0 = 1)
    (c : ℕ) : 0 ≤ rescale h k c := by
  simpa [rescale, h0] using (strictMono_rescale hpos hanti).monotone c.zero_le

/-! ### The Tagalog square (§2.1, §2.3) -/

/-- The Tagalog square (11), *maŋ-* OTHER and *maŋ-* RED- crossed with /b/ and /k/. -/
def tagalogSquare : Square (Prefix × Zuraw2010.StemC) := square .mangOther .mangRed .b .k

/-- The six constraints of §2.3, *NC, *NC̥, *[stem ŋ, *[stem ŋ/n, and the Uniformity constraints
of the two prefixes. -/
def tagalogConstraints : ConstraintSet Candidate (Fin 6) :=
  ![nasSub, starNC, starRootVelar, starRootCorVel, unif .mangOther, unif .mangRed]

-- §2.3, Figure 3
theorem tagalog_independent : tagalogSquare.Independent tagalogConstraints := by
  intro k
  fin_cases k <;> first | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩

/-! ### The inverse harmony (§4.4) -/

/-- The inverse harmony (27) feeds the weighted violations to `h(x) = 1/(1+x)` in place of
maximum entropy's `exp(−x)`. -/
noncomputable def inverseHarmony (w : Fin n → ℝ) (v : Fin n → ℕ) : ℝ :=
  (1 + w ⬝ᵥ (Nat.cast ∘ v))⁻¹

theorem inverseHarmony_pos {w : Fin n → ℝ} (hw : ∀ k, 0 ≤ w k) (v : Fin n → ℕ) :
    0 < inverseHarmony w v := by
  unfold inverseHarmony dotProduct
  exact inv_pos.2 <| add_pos_of_pos_of_nonneg one_pos <|
    sum_nonneg fun k _ ↦ mul_nonneg (hw k) (Nat.cast_nonneg (v k))

/-- On the Tagalog square, inverse harmony satisfies the identity (28) only with equal
prefix-constraint weights or zero stem-nasal weights (§4.4 and footnote 11). -/
theorem inverseHarmony_hz_tagalog_iff {w : Fin 6 → ℝ} (hw : ∀ k, 0 ≤ w k) :
    tagalogSquare.interaction (logOdds (inverseHarmony w) tagalogConstraints .yes .no) = 0 ↔
      w 4 = w 5 ∨ w 2 = 0 ∧ w 3 = 0 := by
  simp [logOdds, inverseHarmony, dotProduct, Fin.sum_univ_six, tagalogSquare, square,
    tagalogConstraints, nasSub, starNC, starRootVelar, starRootCorVel, unif, Zuraw2010.nasSub,
    Zuraw2010.starNC, Zuraw2010.starInitVelar, Zuraw2010.starInitCorVel, project]
  have hp (k : Fin 6) : 0 < 1 + w k := by linarith [hw k]
  have hp' (i j k : Fin 6) : 0 < 1 + (w i + w j + w k) := by linarith [hw i, hw j, hw k]
  have hp'' : 0 < 1 + (w 0 + w 1) := by linarith [hw 0, hw 1]
  have hlog {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : log (x⁻¹ * y) = log y - log x := by
    rw [log_mul (inv_pos.2 hx).ne' hy.ne', log_inv]
    ring
  rw [hlog (hp 4) (hp 0), hlog (hp' 2 3 4) hp'', hlog (hp 5) (hp 0), hlog (hp' 2 3 5) hp'']
  have hA := log_mul (hp' 2 3 4).ne' (hp 5).ne'
  have hB := log_mul (hp 4).ne' (hp' 2 3 5).ne'
  trans (1 + (w 2 + w 3 + w 4)) * (1 + w 5) = (1 + w 4) * (1 + (w 2 + w 3 + w 5))
  · rw [← log_injOn_pos.eq_iff (mul_pos (hp' 2 3 4) (hp 5)) (mul_pos (hp 4) (hp' 2 3 5))]
    constructor <;> intro h <;> linarith
  rw [← sub_eq_zero, show (1 + (w 2 + w 3 + w 4)) * (1 + w 5) - (1 + w 4) * (1 + (w 2 + w 3 + w 5))
    = (w 2 + w 3) * (w 5 - w 4) by ring, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact .inr ⟨by linarith [hw 2, hw 3], by linarith [hw 2, hw 3]⟩
    · exact .inl h.symm
  · rintro (h | ⟨h2, h3⟩)
    · exact .inr h.symm
    · exact .inl (by rw [h2, h3]; ring)

theorem not_separable_inverseHarmony {w : Fin 6 → ℝ} (hw : ∀ k, 0 ≤ w k) (h45 : w 4 ≠ w 5)
    (h2 : w 2 ≠ 0) : ¬ Separable (inverseHarmony w) := fun hH ↦ by
  have := (inverseHarmony_hz_tagalog_iff hw).1 <|
    hH.interaction_logOdds_eq_zero tagalog_independent .yes .no
  tauto

end Magri2025
