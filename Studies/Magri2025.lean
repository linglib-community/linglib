module

public import Studies.ZurawHayes2017

/-!
# Magri (2025): Constraint Interaction in Probabilistic Phonology

The rates of a variable process on four forms crossing two independent factors lie on shifted
sigmoids at shared abscissas [exactly when their logits differ by a constant along the
rows](##Magri2025.exists_shiftedSigmoids_iff). Maximum entropy grammar predicts this [when the
two variants are the only candidates](##Magri2025.interaction_logit_maxEnt), and otherwise [up to
the probability of the others](##Magri2025.abs_interaction_logit_maxEnt_le). A harmony-based
grammar [predicts it exactly when its harmony is separable](##Magri2025.predictsHZ_iff_separable),
a product of positive functions of single constraints' violations; the inverse harmony
$1/(1+x)$ [predicts it on the Tagalog square only for special
weights](##Magri2025.inverseHarmony_hz_tagalog_iff).

## Implementation notes

* A harmony is a function `(Fin n → ℕ) → ℝ` of violation profiles, positive and normalized as
  §4.1 assumes; decreasingness is not needed. `PredictsHZ` is (24) for forms with the two
  candidates YES and NO, read as `true` and `false`. Its log-odds form holds exactly for any
  number of candidates (`Separable.interaction_logOdds_eq_zero`); the logit form holds only
  approximately when there are more, within the bound of `abs_interaction_logit_maxEnt_le`.
* Any separable grammar is the maximum entropy grammar of constraints rescaled by
  `Ĉₖ = −log hₖ(Cₖ)` (`grammar_prod_rpow`), whose violations are no longer integers.
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
candidates YES and NO whose rows and columns are independent relative to the constraints on
those two candidates, the logits of YES differ by the same amount along both rows. -/
def PredictsHZ (H : (Fin n → ℕ) → ℝ) : Prop :=
  ∀ (X : Type) (sq : Square X) (con : ConstraintSet (X × Bool) (Fin n)),
    sq.Independent con true false →
    sq.interaction (fun x ↦ logit ((grammar H con x).real {true})) = 0

/-- A harmony is separable (30) when it is a product of powers of positive unary functions, each
fed the violations of a single constraint. -/
def Separable (H : (Fin n → ℕ) → ℝ) : Prop :=
  ∃ (h : Fin n → ℕ → ℝ) (w : Fin n → ℝ), (∀ k c, 0 < h k c) ∧ ∀ v, H v = ∏ k, h k (v k) ^ w k

-- (30)
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
    {con : ConstraintSet (X × Y) (Fin n)} {a b : Y} (hind : sq.Independent con a b) :
    sq.interaction (logOdds H con a b) = 0 := by
  obtain ⟨g, hg, hgH⟩ := separable_iff_exists_prod.1 hH
  convert hind.interaction_sum_eq_zero fun k v ↦ log (g k v.1) - log (g k v.2) using 2
  ext x
  rw [logOdds, log_div (hH.pos _).ne' (hH.pos _).ne', hgH, hgH,
    log_prod fun k _ ↦ (hg k _).ne', log_prod fun k _ ↦ (hg k _).ne', ← sum_sub_distrib]

-- §5.4
theorem Separable.predictsHZ (hH : Separable H) : PredictsHZ H := by
  intro X sq con hind
  simp_rw [logit_grammar_of_pair hH.pos con _ (a := true) (b := false) (by decide) (by decide)]
  exact hH.interaction_logOdds_eq_zero hind

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
    witnessSquare.Independent (witness u k c) true false := by
  intro j
  by_cases hj : j = k
  · exact .inr ⟨by simp [witness, witnessSquare, hj], by simp [witness, witnessSquare, hj]⟩
  · exact .inl ⟨by simp [witness, witnessSquare, hj], by simp [witness, witnessSquare, hj]⟩

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

-- (14)
theorem grammar_meHarmony {X Y : Type*} [Fintype Y] [MeasurableSpace Y]
    (w : Fin n → ℝ) (con : ConstraintSet (X × Y) (Fin n)) (x : X) :
    grammar (fun v ↦ meHarmony w fun k ↦ v k) con x = maxEnt (con.comap (x, ·)).violations w := by
  simp only [grammar, maxEnt, meHarmony, log_exp]
  congr 1

-- (29)
theorem separable_meHarmony (w : Fin n → ℝ) : Separable fun v ↦ meHarmony w fun k ↦ v k :=
  ⟨fun _ c ↦ exp (-c), w, fun _ _ ↦ exp_pos _, fun v ↦ by
    simp only [meHarmony, ← exp_mul, ← exp_sum, ← sum_neg_distrib, mul_neg, mul_comm]⟩

-- Zero interaction of the log-odds bounds the interaction of the logits by the excess mass.
private theorem abs_interaction_logit_le {X : Type*} {sq : Square X} {p q : X → ℝ}
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) (hpq : ∀ x, p x + q x ≤ 1)
    (h : sq.interaction (fun x ↦ log (p x / q x)) = 0) :
    |sq.interaction fun x ↦ logit (p x)| ≤ sq.sum fun x ↦ (1 - p x - q x) / q x := by
  have hc (x : X) : 0 < 1 - p x := by linarith [hq x, hpq x]
  have hsplit : (fun x ↦ logit (p x)) =
      (fun x ↦ log (p x / q x)) - fun x ↦ log ((1 - p x) / q x) := by
    funext x
    simp only [Pi.sub_apply]
    rw [logit, log_div (hp x).ne' (hc x).ne', log_div (hp x).ne' (hq x).ne',
      log_div (hc x).ne' (hq x).ne']
    ring
  rw [hsplit, map_sub, h, zero_sub, abs_neg]
  refine (Square.abs_interaction_le_sum fun x ↦
    log_nonneg ((one_le_div (hq x)).2 (by linarith [hpq x]))).trans
      (Square.sum_le_sum fun x ↦ ?_)
  rw [sub_div (1 - p x), div_self (hq x).ne']
  exact log_le_sub_one_of_pos (div_pos (hc x) (hq x))

/-- With more candidates than the two variants, MaxEnt predicts HZ's generalization up to the
probability of the other candidates (§3.6): the interaction of the logit rates of `a` is at most
the sum over the square of the other candidates' probability relative to `b`'s. -/
theorem abs_interaction_logit_maxEnt_le {X Y : Type*} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] {sq : Square X} {con : ConstraintSet (X × Y) (Fin n)} {a b : Y}
    (h : sq.Independent con a b) (hab : a ≠ b) (w : Fin n → ℝ) :
    |sq.interaction fun x ↦ logit ((maxEnt (con.comap (x, ·)).violations w).real {a})| ≤
      sq.sum fun x ↦ (1 - (maxEnt (con.comap (x, ·)).violations w).real {a} -
        (maxEnt (con.comap (x, ·)).violations w).real {b}) /
          (maxEnt (con.comap (x, ·)).violations w).real {b} := by
  classical
  have : Nonempty Y := ⟨a⟩
  refine abs_interaction_logit_le (fun x ↦ maxEnt_real_singleton_pos _ w a)
    (fun x ↦ maxEnt_real_singleton_pos _ w b) (fun x ↦ ?_) (h.interaction_logOdds_maxEnt w)
  rw [← sum_pair (f := fun c ↦ (maxEnt (con.comap (x, ·)).violations w).real {c}) hab,
    ← sum_measureReal_singleton_eq_one (maxEnt (con.comap (x, ·)).violations w)]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ measureReal_nonneg

/-- MaxEnt predicts HZ's generalization (22): when the two variants are the only candidates, the
MaxEnt logit rates have zero interaction, for every weighting. -/
theorem interaction_logit_maxEnt {X Y : Type*} [Fintype Y] [DecidableEq Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] {sq : Square X} {con : ConstraintSet (X × Y) (Fin n)} {a b : Y}
    (h : sq.Independent con a b) (hab : a ≠ b) (hY : (univ : Finset Y) = {a, b})
    (w : Fin n → ℝ) :
    sq.interaction (fun x ↦ logit ((maxEnt (con.comap (x, ·)).violations w).real {a})) = 0 := by
  have : Nonempty Y := ⟨a⟩
  have hsum (x : X) : 1 - (maxEnt (con.comap (x, ·)).violations w).real {a} -
      (maxEnt (con.comap (x, ·)).violations w).real {b} = 0 := by
    rw [← sum_measureReal_singleton_eq_one (maxEnt (con.comap (x, ·)).violations w), hY,
      sum_pair hab]
    ring
  simpa [hsum] using abs_interaction_logit_maxEnt_le h hab w

-- §3.6
theorem predictsHZ_meHarmony (w : Fin n → ℝ) : PredictsHZ fun v ↦ meHarmony w fun k ↦ v k := by
  intro X sq con hind
  simp_rw [grammar_meHarmony]
  exact interaction_logit_maxEnt hind (by decide) (by decide) w

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

-- (35)
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
theorem tagalog_independent : tagalogSquare.Independent tagalogConstraints .yes .no := by
  intro k
  fin_cases k <;> first | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩

-- MaxEnt predicts the generalization on the Tagalog square, for every weighting.
example (w : Fin 6 → ℝ) : tagalogSquare.interaction
    (fun x ↦ logit ((maxEnt (tagalogConstraints.comap (x, ·)).violations w).real {.yes})) = 0 :=
  interaction_logit_maxEnt tagalog_independent (by decide) (by decide) w

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
    hH.interaction_logOdds_eq_zero tagalog_independent
  tauto

end Magri2025
