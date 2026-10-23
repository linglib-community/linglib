module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Semantics.Reference.Distinguishing

/-!
# Degen, Hawkins, Graf, Kreiss and Goodman (2020): When Redundancy Is Useful: A Bayesian Approach to "Overinformative" Referring Expressions

Degen and colleagues' rational speech act model with a continuous semantics. A referring
expression holds of an object to a degree in the unit interval. An adjective of semantic value `x`
holds to degree `x` of the objects in its Boolean extension and to degree `1 − x` of the others,
and an expression of two adjectives multiplies their degrees. The literal listener normalizes the
degrees over the objects of the context, and the speaker chooses an expression in proportion to
the exponential of its utility, the log of the listener's probability of the intended object less
the cost of the expression. An adjective that the Boolean semantics makes redundant then adds
information, and adds more the less noisy it is.

## Main statements

* `overmodification_odds_lt_iff`: among the three pins of the paper's first figure the speaker
  adds a redundant colour to a sufficient size more readily than a redundant size to a sufficient
  colour exactly when size is the noisier of the two, at every positive rationality and when the
  two redundant adjectives cost the same.
* `color_overmodification_iff`, `size_overmodification_iff`: without cost the redundant
  expression is preferred to the sufficient one exactly when the semantic value of the redundant
  adjective exceeds one half.
* `boolean_no_preference`: with Boolean values the redundant adjective adds nothing.

## Implementation notes

* `S1` is `RSA.speaker`, whose rationality `α` scales the whole utility. The paper weights
  informativeness and cost separately and notes that the two parameterizations are equivalent.
* The listener and the speaker take any graded meaning, so the typicality semantics of the
  paper's third experiment is the same model at another meaning, and `S1_real_lt_iff` is its
  preference for the term of greater utility.

## TODO

* Tables 2 and 3 do not follow from Equation (1) at the stated values x_size = .8 and
  x_colour = .99. Their values match a listener proportional to the exponential of the meaning.
  The theorems follow the equations.
* The regression coefficients and the fitted parameters of the three experiments are not encoded.

## References

* [degen-etal-2020]
* [frank-goodman-2012]
-/

@[expose] public section

namespace DegenEtAl2020

open MeasureTheory ProbabilityTheory RSA

/-! ### Continuous semantics -/

/-- An adjective of semantic value `x` holds to degree `x` of an object in its Boolean extension
and to degree `1 − x` of any other, (6). -/
def noisy (x : ℝ) (p : Prop) [Decidable p] : ℝ := if p then x else 1 - x

theorem noisy_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (p : Prop) [Decidable p] :
    0 ≤ noisy x p := by
  unfold noisy; split_ifs <;> linarith

/-! ### The gain of a redundant adjective -/

/-- In a display where the target alone has the sufficient property, one competitor shares the
redundant property with it and `b` distractors share neither, the redundant adjective multiplies
the literal listener's probability of the target by this factor, where `xs` is the semantic value
of the sufficient adjective and `xr` that of the redundant one. -/
noncomputable def gain (b : ℕ) (xs xr : ℝ) : ℝ :=
  xr * (xs + (b + 1) * (1 - xs)) / (xr + b * (1 - xs) * (1 - xr))

section Gain

variable {b : ℕ} {xs xr xr' x₁ x₂ : ℝ}

private theorem gain_den_pos (hs1 : xs ≤ 1) (hr0 : 0 < xr) (hr1 : xr ≤ 1) :
    0 < xr + b * (1 - xs) * (1 - xr) :=
  add_pos_of_pos_of_nonneg hr0
    (mul_nonneg (mul_nonneg b.cast_nonneg (sub_nonneg.2 hs1)) (sub_nonneg.2 hr1))

private theorem gain_num_pos (hs0 : 0 < xs) (hs1 : xs ≤ 1) : 0 < xs + ((b : ℝ) + 1) * (1 - xs) :=
  add_pos_of_pos_of_nonneg hs0 (mul_nonneg (by positivity) (sub_nonneg.2 hs1))

theorem gain_pos (hs0 : 0 < xs) (hs1 : xs ≤ 1) (hr0 : 0 < xr) (hr1 : xr ≤ 1) :
    0 < gain b xs xr :=
  div_pos (mul_pos hr0 (gain_num_pos hs0 hs1)) (gain_den_pos hs1 hr0 hr1)

theorem div_div_eq_gain_one (hs0 : 0 < xs) (hs1 : xs ≤ 1) (hr0 : 0 < xr) :
    xs * xr / (1 - xs + xs * xr) / (xs / (2 - xs)) = gain 1 xs xr := by
  have h1 : 0 < 1 - xs + xs * xr := by nlinarith
  have h2 : 0 < xr + 1 * (1 - xs) * (1 - xr) := by nlinarith
  rw [gain, Nat.cast_one, div_div_div_eq, div_eq_div_iff (mul_pos h1 hs0).ne' h2.ne']
  ring

theorem gain_one_left (hr : xr ≠ 0) : gain b 1 xr = 1 := by
  simp [gain, hr]

theorem one_lt_gain_iff (hb : 0 < b) (hs1 : xs < 1) (hr0 : 0 < xr) (hr1 : xr ≤ 1) :
    1 < gain b xs xr ↔ 1/2 < xr := by
  rw [gain, one_lt_div (gain_den_pos hs1.le hr0 hr1), ← sub_pos,
    show xr * (xs + (b + 1) * (1 - xs)) - (xr + b * (1 - xs) * (1 - xr)) =
      (2 * xr - 1) * (b * (1 - xs)) by ring,
    mul_pos_iff_of_pos_right (mul_pos (Nat.cast_pos.2 hb) (sub_pos.2 hs1))]
  constructor <;> intro h <;> linarith

theorem gain_lt_gain_iff (hb : 0 < b) (hs0 : 0 < xs) (hs1 : xs < 1) (hr0 : 0 < xr)
    (hr1 : xr ≤ 1) (hr0' : 0 < xr') (hr1' : xr' ≤ 1) :
    gain b xs xr < gain b xs xr' ↔ xr < xr' := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  rw [gain, gain, div_lt_div_iff₀ (gain_den_pos hs1.le hr0 hr1) (gain_den_pos hs1.le hr0' hr1'),
    ← sub_pos,
    show xr' * (xs + (b + 1) * (1 - xs)) * (xr + b * (1 - xs) * (1 - xr)) -
        xr * (xs + (b + 1) * (1 - xs)) * (xr' + b * (1 - xs) * (1 - xr')) =
      (xr' - xr) * ((xs + (b + 1) * (1 - xs)) * (b * (1 - xs))) by ring,
    mul_pos_iff_of_pos_right (mul_pos (gain_num_pos hs0 hs1.le) (mul_pos hb' (sub_pos.2 hs1))),
    sub_pos]

theorem gain_swap_lt_iff (hb : 0 < b) (h₁0 : 0 < x₁) (h₁1 : x₁ ≤ 1) (h₂0 : 0 < x₂)
    (h₂1 : x₂ ≤ 1) : gain b x₂ x₁ < gain b x₁ x₂ ↔ x₁ < x₂ := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hk : 0 < b * (x₁ * x₂ + (b + 1) * ((1 - x₁) * (1 - x₂))) :=
    mul_pos hb' (add_pos_of_pos_of_nonneg (mul_pos h₁0 h₂0)
      (mul_nonneg (by positivity) (mul_nonneg (sub_nonneg.2 h₁1) (sub_nonneg.2 h₂1))))
  rw [gain, gain, div_lt_div_iff₀ (gain_den_pos h₂1 h₁0 h₁1) (gain_den_pos h₁1 h₂0 h₂1), ← sub_pos,
    show x₂ * (x₁ + (b + 1) * (1 - x₁)) * (x₁ + b * (1 - x₂) * (1 - x₁)) -
        x₁ * (x₂ + (b + 1) * (1 - x₂)) * (x₂ + b * (1 - x₁) * (1 - x₂)) =
      (x₂ - x₁) * (b * (x₁ * x₂ + (b + 1) * ((1 - x₁) * (1 - x₂)))) by ring,
    mul_pos_iff_of_pos_right hk, sub_pos]

end Gain

/-! ### Listener and speaker -/

section Model

variable {E U : Type*} [Fintype E]

private theorem sum_pos_of_pos {m : U → E → ℝ} {u : U} {o : E} (hm : ∀ v o', 0 ≤ m v o')
    (h : 0 < m u o) : 0 < ∑ o', m u o' :=
  Finset.sum_pos' (fun o' _ ↦ hm u o') ⟨o, Finset.mem_univ o, h⟩

variable [MeasurableSpace E] [MeasurableSingletonClass E] [Fintype U] [MeasurableSpace U]
  [MeasurableSingletonClass U]

/-- The literal listener (1) normalizes the meaning of an expression over the objects at a
uniform prior. -/
noncomputable def L0 (m : U → E → ℝ) : Kernel U E :=
  Kernel.ofDensity (uniformOn Set.univ) fun u o ↦ ENNReal.ofReal (m u o)

instance (m : U → E → ℝ) : IsFiniteKernel (L0 m) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofDensity _ _))

/-- The speaker of (3) and (4) at rationality `α` chooses an expression in proportion to the
exponential of `α` times its utility, the log of the listener's probability of the object less
the cost `C`. -/
noncomputable def S1 (α : ℝ) (C : U → ℝ) (m : U → E → ℝ) : Kernel E U :=
  speaker α C (L0 m) Measure.dirac

instance (α : ℝ) (C : U → ℝ) (m : U → E → ℝ) : IsFiniteKernel (S1 α C m) :=
  inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

variable {m : U → E → ℝ} {α : ℝ} {C : U → ℝ} {u u' : U} {o : E}

theorem S1_apply_singleton_of_equiv {U' : Type*} [Fintype U'] [MeasurableSpace U']
    [MeasurableSingletonClass U'] (τ : U ≃ U') (α : ℝ) (C : U' → ℝ) {m' : U' → E → ℝ}
    (h : ∀ v, m' (τ v) = m v) (o : E) (u : U) :
    S1 α C m' o {τ u} = S1 α (C ∘ τ) m o {u} :=
  speaker_dirac_apply_singleton_of_equiv τ α C (fun v ↦ by
    rw [L0, L0, Kernel.ofDensity_apply, Kernel.ofDensity_apply, h]) u

variable [Nonempty E]

theorem L0_apply (hm : ∀ o', 0 ≤ m u o') (hpos : 0 < ∑ o', m u o') (o : E) :
    L0 m u {o} = ENNReal.ofReal (m u o / ∑ o', m u o') :=
  Kernel.ofDensity_uniformOn_ofReal_apply_singleton _ u o hm hpos

theorem L0_real_singleton (hm : ∀ o', 0 ≤ m u o') (hpos : 0 < ∑ o', m u o') (o : E) :
    (L0 m u).real {o} = m u o / ∑ o', m u o' := by
  rw [measureReal_def, L0_apply hm hpos, ENNReal.toReal_ofReal (div_nonneg (hm o) hpos.le)]

private theorem L0_ne_zero (hm : ∀ v o', 0 ≤ m v o') (h : 0 < m u o) : L0 m u {o} ≠ 0 := by
  rw [L0_apply (hm u) (sum_pos_of_pos hm h)]
  exact (ENNReal.ofReal_pos.2 (div_pos h (sum_pos_of_pos hm h))).ne'

private theorem L0_eq_zero (h : m u o = 0) : L0 m u {o} = 0 := by
  rw [L0, Kernel.ofDensity_uniformOn_apply_singleton, h, ENNReal.ofReal_zero, ENNReal.zero_div]

theorem S1_real_div (hα : 0 ≤ α) (hm : ∀ v o', 0 ≤ m v o') (hu : 0 < m u o) (hu' : 0 < m u' o) :
    (S1 α C m o).real {u'} / (S1 α C m o).real {u} =
      ((m u' o / ∑ o', m u' o') / (m u o / ∑ o', m u o')) ^ α *
        Real.exp (-(α * (C u' - C u))) := by
  rw [S1, speaker_dirac_real_singleton_div hα (L0_ne_zero hm hu), ← measureReal_def,
    ← measureReal_def, L0_real_singleton (hm u) (sum_pos_of_pos hm hu),
    L0_real_singleton (hm u') (sum_pos_of_pos hm hu')]

/-- The speaker prefers the expression of greater utility. -/
theorem S1_real_lt_iff (hα : 0 < α) (hm : ∀ v o', 0 ≤ m v o') (hu : 0 < m u o)
    (hu' : 0 < m u' o) :
    (S1 α C m o).real {u} < (S1 α C m o).real {u'} ↔
      Real.log (m u o / ∑ o', m u o') - C u < Real.log (m u' o / ∑ o', m u' o') - C u' := by
  rw [S1, speaker_dirac_real_singleton_lt_iff_log hα (L0_ne_zero hm hu) (L0_ne_zero hm hu'),
    ← measureReal_def, ← measureReal_def, L0_real_singleton (hm u) (sum_pos_of_pos hm hu),
    L0_real_singleton (hm u') (sum_pos_of_pos hm hu')]

theorem S1_real_of_pair (hα : 0 < α) (huu' : u ≠ u') (hm : ∀ v o', 0 ≤ m v o') (hu : 0 < m u o)
    (hu' : 0 < m u' o) (hsupp : ∀ v, 0 < m v o → v = u ∨ v = u') :
    (S1 α C m o).real {u} = Real.sigmoid (α * ((Real.log (m u o / ∑ o', m u o') - C u) -
      (Real.log (m u' o / ∑ o', m u' o') - C u'))) := by
  rw [S1, speaker_dirac_real_singleton_of_pair hα huu' (L0_ne_zero hm hu) (L0_ne_zero hm hu')
      fun v hv ↦ hsupp v ((hm v o).lt_of_ne fun h ↦ hv (L0_eq_zero h.symm)),
    ← measureReal_def, ← measureReal_def, L0_real_singleton (hm u) (sum_pos_of_pos hm hu),
    L0_real_singleton (hm u') (sum_pos_of_pos hm hu')]

theorem S1_real_eq_one (hα : 0 < α) (hm : ∀ v o', 0 ≤ m v o') (hu : 0 < m u o)
    (hother : ∀ v, v ≠ u → m v o = 0) : (S1 α C m o).real {u} = 1 := by
  rw [measureReal_def, S1, speaker_dirac_apply_singleton_eq_one hα (L0_ne_zero hm hu)
    fun v hv ↦ L0_eq_zero (hother v hv), ENNReal.toReal_one]

theorem distinguishes_L0_iff (hm : ∀ o', 0 ≤ m u o') (hpos : 0 < ∑ o', m u o') (D : Finset E)
    (r : E) :
    Distinguishes (fun u o ↦ L0 m u {o}) D r u ↔ Distinguishes m D r u :=
  distinguishes_comp_iff (φ := fun x ↦ ENNReal.ofReal (x / ∑ o', m u o'))
    (s := Set.Ici 0) (fun _ ha _ _ hab ↦ (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (div_nonneg ha hpos.le)).2 ((div_lt_div_iff_of_pos_right hpos).2 hab))
    hm (L0_apply hm hpos)

end Model

/-! ### The pins of the first figure -/

/-- The sizes of the pins. -/
inductive Size where
  | big
  | small
  deriving DecidableEq, Repr

/-- The colours of the pins. -/
inductive Color where
  | blue
  | red
  deriving DecidableEq, Repr

/-- The size-sufficient context has three pins, the target small blue pin, a big blue one and
a big red one. -/
inductive Pin where
  | bigBlue
  | bigRed
  | smallBlue
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Pin := ⊤
instance : DiscreteMeasurableSpace Pin := ⟨fun _ ↦ trivial⟩

/-- The size of a pin. -/
def Pin.size : Pin → Size
  | .bigBlue | .bigRed => .big
  | .smallBlue => .small

/-- The colour of a pin. -/
def Pin.color : Pin → Color
  | .bigBlue | .smallBlue => .blue
  | .bigRed => .red

/-- The seven referring expressions name a size, a colour, or both, each followed by
*pin*. -/
inductive Utterance where
  | big
  | small
  | blue
  | red
  | bigBlue
  | bigRed
  | smallBlue
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ ↦ trivial⟩

/-- The size an expression names, if any. -/
def Utterance.size : Utterance → Option Size
  | .big | .bigBlue | .bigRed => some .big
  | .small | .smallBlue => some .small
  | .blue | .red => none

/-- The colour an expression names, if any. -/
def Utterance.color : Utterance → Option Color
  | .blue | .bigBlue | .smallBlue => some .blue
  | .red | .bigRed => some .red
  | .big | .small => none

/-- The meaning of an expression is the product, over the adjectives it contains, of the degree
to which each holds of the pin, (5) and (6), with semantic value `xs` for size and `xc` for
colour. -/
def meaning (xs xc : ℝ) (u : Utterance) (o : Pin) : ℝ :=
  (u.size.elim 1 fun s ↦ noisy xs (o.size = s)) * (u.color.elim 1 fun c ↦ noisy xc (o.color = c))

section Overmodification

variable {xs xc α : ℝ} {C : Utterance → ℝ}

theorem meaning_nonneg (hs0 : 0 ≤ xs) (hs1 : xs ≤ 1) (hc0 : 0 ≤ xc) (hc1 : xc ≤ 1)
    (u : Utterance) (o : Pin) : 0 ≤ meaning xs xc u o := by
  refine mul_nonneg ?_ ?_
  · cases u.size <;> [exact zero_le_one; exact noisy_nonneg hs0 hs1 _]
  · cases u.color <;> [exact zero_le_one; exact noisy_nonneg hc0 hc1 _]

private theorem sum_pin (f : Pin → ℝ) : ∑ o, f o = f .bigBlue + f .bigRed + f .smallBlue := by
  rw [show (Finset.univ : Finset Pin) = {.bigBlue, .bigRed, .smallBlue} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

private theorem row_small : ∑ o, meaning xs xc .small o = 2 - xs := by
  rw [sum_pin]; simp [meaning, noisy, Utterance.size, Utterance.color, Pin.size]
  ring

private theorem row_smallBlue : ∑ o, meaning xs xc .smallBlue o = (1 - xs) + xs * xc := by
  rw [sum_pin]; simp [meaning, noisy, Utterance.size, Utterance.color, Pin.size, Pin.color]
  ring

private theorem row_red : ∑ o, meaning xs xc .red o = 2 - xc := by
  rw [sum_pin]; simp [meaning, noisy, Utterance.size, Utterance.color, Pin.color]
  ring

private theorem row_bigRed : ∑ o, meaning xs xc .bigRed o = xs + (1 - xs) * (1 - xc) := by
  rw [sum_pin]; simp [meaning, noisy, Utterance.size, Utterance.color, Pin.size, Pin.color]
  ring

private theorem meaning_small : meaning xs xc .small .smallBlue = xs := by
  simp [meaning, noisy, Utterance.size, Utterance.color, Pin.size]

private theorem meaning_smallBlue : meaning xs xc .smallBlue .smallBlue = xs * xc := by
  simp [meaning, noisy, Utterance.size, Utterance.color, Pin.size, Pin.color]

private theorem meaning_red : meaning xs xc .red .bigRed = xc := by
  simp [meaning, noisy, Utterance.size, Utterance.color, Pin.color]

private theorem meaning_bigRed : meaning xs xc .bigRed .bigRed = xs * xc := by
  simp [meaning, noisy, Utterance.size, Utterance.color, Pin.size, Pin.color]

theorem gain_smallBlue (hs0 : 0 < xs) (hs1 : xs ≤ 1) (hc0 : 0 < xc) :
    (meaning xs xc .smallBlue .smallBlue / ∑ o, meaning xs xc .smallBlue o) /
      (meaning xs xc .small .smallBlue / ∑ o, meaning xs xc .small o) = gain 1 xs xc := by
  rw [row_small, row_smallBlue, meaning_small, meaning_smallBlue]
  exact div_div_eq_gain_one hs0 hs1 hc0

theorem gain_bigRed (hs0 : 0 < xs) (hc0 : 0 < xc) (hc1 : xc ≤ 1) :
    (meaning xs xc .bigRed .bigRed / ∑ o, meaning xs xc .bigRed o) /
      (meaning xs xc .red .bigRed / ∑ o, meaning xs xc .red o) = gain 1 xc xs := by
  have h1 : 0 < xs + (1 - xs) * (1 - xc) := by nlinarith
  have h2 : 0 < xs + 1 * (1 - xc) * (1 - xs) := by nlinarith
  rw [row_red, row_bigRed, meaning_red, meaning_bigRed, gain, Nat.cast_one, div_div_div_eq,
    div_eq_div_iff (mul_pos h1 hc0).ne' h2.ne']
  ring

/-- For the small blue pin and without cost, the redundant *small blue* is preferred to the
sufficient *small* exactly when the semantic value of colour exceeds one half, whatever that of
size short of Boolean. -/
theorem color_overmodification_iff (hα : 0 < α) (hs0 : 0 < xs) (hs1 : xs < 1) (hc0 : 0 < xc)
    (hc1 : xc ≤ 1) :
    (S1 α 0 (meaning xs xc) .smallBlue).real {.small} <
      (S1 α 0 (meaning xs xc) .smallBlue).real {.smallBlue} ↔ 1/2 < xc := by
  have h : 0 < meaning xs xc .small .smallBlue / ∑ o, meaning xs xc .small o :=
    div_pos (by rwa [meaning_small]) (by rw [row_small]; linarith)
  have h' : 0 < meaning xs xc .smallBlue .smallBlue / ∑ o, meaning xs xc .smallBlue o :=
    div_pos (by rw [meaning_smallBlue]; positivity) (by rw [row_smallBlue]; nlinarith)
  rw [S1_real_lt_iff hα (meaning_nonneg hs0.le hs1.le hc0.le hc1) (by rwa [meaning_small])
      (by rw [meaning_smallBlue]; positivity), Pi.zero_apply, Pi.zero_apply, sub_zero, sub_zero,
    Real.log_lt_log_iff h h', ← one_lt_div h, gain_smallBlue hs0 hs1.le hc0,
    one_lt_gain_iff one_pos hs1 hc0 hc1]

/-- For the big red pin and without cost, the redundant *big red* is preferred to the sufficient
*red* exactly when the semantic value of size exceeds one half, whatever that of colour short of
Boolean. -/
theorem size_overmodification_iff (hα : 0 < α) (hs0 : 0 < xs) (hs1 : xs ≤ 1) (hc0 : 0 < xc)
    (hc1 : xc < 1) :
    (S1 α 0 (meaning xs xc) .bigRed).real {.red} <
      (S1 α 0 (meaning xs xc) .bigRed).real {.bigRed} ↔ 1/2 < xs := by
  have h : 0 < meaning xs xc .red .bigRed / ∑ o, meaning xs xc .red o :=
    div_pos (by rwa [meaning_red]) (by rw [row_red]; linarith)
  have h' : 0 < meaning xs xc .bigRed .bigRed / ∑ o, meaning xs xc .bigRed o :=
    div_pos (by rw [meaning_bigRed]; positivity) (by rw [row_bigRed]; nlinarith)
  rw [S1_real_lt_iff hα (meaning_nonneg hs0.le hs1 hc0.le hc1.le) (by rwa [meaning_red])
      (by rw [meaning_bigRed]; positivity), Pi.zero_apply, Pi.zero_apply, sub_zero, sub_zero,
    Real.log_lt_log_iff h h', ← one_lt_div h, gain_bigRed hs0 hc0 hc1.le,
    one_lt_gain_iff one_pos hc1 hs0 hs1]

theorem overmodification_odds_lt_iff (hα : 0 < α) (hs0 : 0 < xs) (hs1 : xs ≤ 1) (hc0 : 0 < xc)
    (hc1 : xc ≤ 1) (hC : C .smallBlue - C .small = C .bigRed - C .red) :
    (S1 α C (meaning xs xc) .bigRed).real {.bigRed} /
        (S1 α C (meaning xs xc) .bigRed).real {.red} <
      (S1 α C (meaning xs xc) .smallBlue).real {.smallBlue} /
        (S1 α C (meaning xs xc) .smallBlue).real {.small} ↔ xs < xc := by
  have hnn := meaning_nonneg hs0.le hs1 hc0.le hc1
  rw [S1_real_div hα.le hnn (by rwa [meaning_red]) (by rw [meaning_bigRed]; positivity),
    S1_real_div hα.le hnn (by rwa [meaning_small]) (by rw [meaning_smallBlue]; positivity), hC,
    mul_lt_mul_iff_left₀ (Real.exp_pos _), gain_smallBlue hs0 hs1 hc0,
    gain_bigRed hs0 hc0 hc1,
    Real.rpow_lt_rpow_iff (gain_pos hc0 hc1 hs0 hs1).le (gain_pos hs0 hs1 hc0 hc1).le hα,
    gain_swap_lt_iff one_pos hs0 hs1 hc0 hc1]

theorem small_distinguishes_iff :
    Distinguishes (meaning xs xc) {.bigBlue, .bigRed} .smallBlue .small ↔ 1/2 < xs := by
  simp [Distinguishes, meaning, noisy, Utterance.size, Utterance.color, Pin.size]
  constructor <;> intro h <;> linarith

theorem smallBlue_distinguishes_iff (hc : 0 < xc) :
    Distinguishes (meaning xs xc) {.bigBlue, .bigRed} .smallBlue .smallBlue ↔
      1/2 < xs ∧ 1 < xs + xc := by
  simp [Distinguishes, meaning, noisy, Utterance.size, Utterance.color, Pin.size,
    Pin.color]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩

theorem boolean_no_preference (α : ℝ) :
    (S1 α 0 (meaning 1 1) .smallBlue).real {.small} =
      (S1 α 0 (meaning 1 1) .smallBlue).real {.smallBlue} := by
  have hnn := meaning_nonneg (xs := 1) (xc := 1) zero_le_one le_rfl zero_le_one le_rfl
  have h1 := L0_apply (hnn .small) (by rw [row_small]; norm_num) Pin.smallBlue
  have h2 := L0_apply (hnn .smallBlue) (by rw [row_smallBlue]; norm_num) Pin.smallBlue
  rw [row_small, meaning_small] at h1
  rw [row_smallBlue, meaning_smallBlue] at h2
  norm_num at h1 h2
  simp only [S1, measureReal_def, speaker_dirac_zero_apply_singleton, h1, h2]

end Overmodification

end DegenEtAl2020
