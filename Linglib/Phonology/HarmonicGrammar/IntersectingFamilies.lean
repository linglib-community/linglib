module

public import Linglib.Phonology.HarmonicGrammar.MaxEnt
public import Mathlib.LinearAlgebra.Pi

/-!
# Intersecting constraint families

Two constraint families intersect ([zuraw-hayes-2017]) when a variable process is conditioned by
two binary factors and each constraint is sensitive to at most one of them: arranging the four
underlying forms that cross the factors into a square, each constraint is insensitive to the rows
or to the columns, on the two surface variants of each form, the variant where the process
applies and the one where it does not (§2.4 of [magri-2025]). [zuraw-hayes-2017] and
[hayes-2022] observe that the rates of application to the four forms then fit two shifted
sigmoids at shared abscissas. [magri-2025] restates the generalization on logit rates: the
difference between the logit rates of two forms in one row does not depend on the row (13).
Equivalently, the interaction contrast of the logit rates on the square vanishes; this file
states the generalization so, as the kernel of a linear functional.

A function of the two variants' violations that is a sum of per-constraint terms has zero
interaction whenever the families intersect, since each term is insensitive to one dimension.
The MaxEnt log-odds of the two variants is such a sum, the weighted violation differences, so it
has zero interaction for every weighting and every candidate set. The logit rate of application
is that log-odds when the two variants are the only candidates, and MaxEnt then predicts the
generalization exactly. Other candidates take part of the probability, and the interaction of
the logit rates is bounded by the mass they take relative to the variant where the process does
not apply, so the generalization holds approximately when that mass is small (§3.6).

## Main definitions

* `HarmonicGrammar.Square`: four underlying forms crossing two binary factors, (12) of
  [magri-2025].
* `Square.interaction`: the interaction contrast `f tl - f tr - f bl + f br`, a linear
  functional on the functions of the forms.
* `Square.InsensitiveToRow`, `Square.InsensitiveToCol`, `Square.Independent`: the independence
  of the rows and columns relative to a constraint set, on two surface variants.

## Main results

* `Square.Independent.interaction_sum_eq_zero`: under independence, a sum of per-constraint terms
  has zero interaction.
* `Square.Independent.interaction_logOdds_maxEnt`: the MaxEnt log-odds of the two variants have
  zero interaction.
* `Square.Independent.interaction_logit_maxEnt`: with two candidates, MaxEnt predicts the
  generalization, (22) of [magri-2025].
* `Square.Independent.abs_interaction_logit_maxEnt_le`: with more candidates, the interaction of
  the logit rates is bounded by the other candidates' mass relative to the second variant.

## References

* [zuraw-hayes-2017]
* [hayes-2022]
* [magri-2025]
-/

@[expose] public section

namespace HarmonicGrammar

open Real OptimalityTheory Function MeasureTheory

/-- Four underlying forms crossing two binary factors, rows by columns ((12) of [magri-2025]). -/
structure Square (X : Type*) where
  /-- The top-left form. -/
  tl : X
  /-- The top-right form. -/
  tr : X
  /-- The bottom-left form. -/
  bl : X
  /-- The bottom-right form. -/
  br : X

namespace Square

variable {X Y α β R : Type*} {n : ℕ} (sq : Square X)

/-- The square with its rows and columns exchanged. -/
def transpose : Square X := ⟨sq.tl, sq.bl, sq.tr, sq.br⟩

/-! ### Independence -/

/-- `f` is insensitive to the rows when it agrees on the two forms of each column (Figure 4a of
[magri-2025]). -/
def InsensitiveToRow (f : X → α) : Prop := f sq.tl = f sq.bl ∧ f sq.tr = f sq.br

/-- `f` is insensitive to the columns when it agrees on the two forms of each row (Figure 4b of
[magri-2025]). -/
def InsensitiveToCol (f : X → α) : Prop := f sq.tl = f sq.tr ∧ f sq.bl = f sq.br

/-- The rows and columns are independent dimensions relative to `con` on the surface variants
`a` and `b` (§2.4 of [magri-2025]): each constraint is insensitive to the rows or to the columns,
reading its violations of the two variants of a form. -/
def Independent (con : ConstraintSet (X × Y) (Fin n)) (a b : Y) : Prop :=
  ∀ k, sq.InsensitiveToRow (fun x ↦ (con k (x, a), con k (x, b))) ∨
    sq.InsensitiveToCol (fun x ↦ (con k (x, a), con k (x, b)))

variable {sq}

theorem InsensitiveToRow.comp {f : X → α} (h : sq.InsensitiveToRow f) (g : α → β) :
    sq.InsensitiveToRow (g ∘ f) :=
  ⟨congrArg g h.1, congrArg g h.2⟩

theorem InsensitiveToCol.comp {f : X → α} (h : sq.InsensitiveToCol f) (g : α → β) :
    sq.InsensitiveToCol (g ∘ f) :=
  ⟨congrArg g h.1, congrArg g h.2⟩

/-! ### The interaction contrast -/

section Interaction

variable [CommRing R]

variable (sq) in
/-- The interaction contrast is the difference of `f` along the top row minus its difference
along the bottom row. -/
def interaction : (X → R) →ₗ[R] R :=
  .proj sq.tl - .proj sq.tr - .proj sq.bl + .proj sq.br

@[simp] theorem interaction_apply (f : X → R) :
    sq.interaction f = f sq.tl - f sq.tr - f sq.bl + f sq.br :=
  rfl

/-- The interaction vanishes iff the differences along the two rows agree ((13) of
[magri-2025]). -/
theorem interaction_eq_zero_iff {f : X → R} :
    sq.interaction f = 0 ↔ f sq.tl - f sq.tr = f sq.bl - f sq.br := by
  rw [interaction_apply]
  constructor <;> intro h <;> linear_combination h

/-- The interaction vanishes iff the differences along the two columns agree ((10) of
[magri-2025]). -/
theorem interaction_eq_zero_iff' {f : X → R} :
    sq.interaction f = 0 ↔ f sq.tl - f sq.bl = f sq.tr - f sq.br := by
  rw [interaction_apply]
  constructor <;> intro h <;> linear_combination h

@[simp] theorem interaction_transpose (f : X → R) :
    sq.transpose.interaction f = sq.interaction f := by
  simp only [transpose, interaction_apply]
  ring

theorem InsensitiveToRow.interaction_eq_zero {f : X → R} (h : sq.InsensitiveToRow f) :
    sq.interaction f = 0 := by
  rw [interaction_apply, h.1, h.2]
  ring

theorem InsensitiveToCol.interaction_eq_zero {f : X → R} (h : sq.InsensitiveToCol f) :
    sq.interaction f = 0 := by
  rw [interaction_apply, h.1, h.2]
  ring

/-- Under independence, a sum of per-constraint terms, each reading only its constraint's
violations of the two variants of a form, has zero interaction. -/
theorem Independent.interaction_sum_eq_zero {con : ConstraintSet (X × Y) (Fin n)} {a b : Y}
    (h : sq.Independent con a b) (φ : Fin n → ℕ × ℕ → R) :
    sq.interaction (fun x ↦ ∑ k, φ k (con k (x, a), con k (x, b))) = 0 := by
  rw [show (fun x ↦ ∑ k, φ k (con k (x, a), con k (x, b))) =
      ∑ k, φ k ∘ fun x ↦ (con k (x, a), con k (x, b)) by ext; simp, map_sum]
  exact Finset.sum_eq_zero fun k _ ↦ (h k).elim (·.comp _ |>.interaction_eq_zero)
    (·.comp _ |>.interaction_eq_zero)

theorem Independent.interaction_harmonyScore_sub {con : ConstraintSet (X × Y) (Fin n)}
    {a b : Y} (h : sq.Independent con a b) (w : Fin n → R) :
    sq.interaction (fun x ↦ harmonyScore con w (x, a) - harmonyScore con w (x, b)) = 0 := by
  convert h.interaction_sum_eq_zero (fun k v ↦ w k * v.2 - w k * v.1) using 2
  ext x
  simp only [harmonyScore_eq_neg_sum, Finset.sum_sub_distrib]
  ring

end Interaction

/-- Under independence, the MaxEnt log-odds of the two variants have zero interaction, for every
weighting and every candidate set. -/
theorem Independent.interaction_logOdds_maxEnt [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] {con : ConstraintSet (X × Y) (Fin n)} {a b : Y}
    (h : sq.Independent con a b) (w : Fin n → ℝ) :
    sq.interaction (fun x ↦ log ((maxEnt (con.comap (x, ·)).violations w).real {a} /
      (maxEnt (con.comap (x, ·)).violations w).real {b})) = 0 := by
  simpa only [log_maxEnt_real_singleton_div, harmony_violations, harmonyScore_comap] using
    h.interaction_harmonyScore_sub w

/-- Where the log-odds of `p` against `q` have zero interaction and `q` is at most the complement
of `p`, the interaction of the logits of `p` is bounded by the excess of that complement over
`q`, relative to `q`. -/
private theorem abs_interaction_logit_le {p q : X → ℝ} (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hpq : ∀ x, p x + q x ≤ 1) (h : sq.interaction (fun x ↦ log (p x / q x)) = 0) :
    |sq.interaction (fun x ↦ log (p x / (1 - p x)))| ≤
      ([sq.tl, sq.tr, sq.bl, sq.br].map fun x ↦ (1 - p x - q x) / q x).sum := by
  have hc (x : X) : 0 < 1 - p x := by linarith [hq x, hpq x]
  have hsplit : (fun x ↦ log (p x / (1 - p x))) =
      (fun x ↦ log (p x / q x)) - fun x ↦ log ((1 - p x) / q x) := by
    funext x
    show log (p x / (1 - p x)) = log (p x / q x) - log ((1 - p x) / q x)
    rw [log_div (hp x).ne' (hc x).ne', log_div (hp x).ne' (hq x).ne',
      log_div (hc x).ne' (hq x).ne']
    ring
  have h0 (x : X) : 0 ≤ log ((1 - p x) / q x) :=
    log_nonneg ((one_le_div (hq x)).2 (by linarith [hpq x]))
  have h1 (x : X) : log ((1 - p x) / q x) ≤ (1 - p x - q x) / q x := by
    rw [sub_div (1 - p x), div_self (hq x).ne']
    exact log_le_sub_one_of_pos (div_pos (hc x) (hq x))
  rw [hsplit, map_sub, h, zero_sub, abs_neg]
  simp only [interaction_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  rw [abs_le]
  constructor <;> linarith [h0 sq.tl, h0 sq.tr, h0 sq.bl, h0 sq.br, h1 sq.tl, h1 sq.tr,
    h1 sq.bl, h1 sq.br]

/-- With more candidates than the two variants, MaxEnt predicts HZ's generalization up to the
probability of the other candidates (§3.6 of [magri-2025]): the interaction of the logit rates of
`a` is at most the sum, over the four forms, of the other candidates' probability relative to
`b`'s. -/
theorem Independent.abs_interaction_logit_maxEnt_le [Fintype Y] [DecidableEq Y]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] {con : ConstraintSet (X × Y) (Fin n)}
    {a b : Y} (h : sq.Independent con a b) (hab : a ≠ b) (w : Fin n → ℝ) :
    |sq.interaction (fun x ↦ log ((maxEnt (con.comap (x, ·)).violations w).real {a} /
      (1 - (maxEnt (con.comap (x, ·)).violations w).real {a})))| ≤
      ([sq.tl, sq.tr, sq.bl, sq.br].map fun x ↦
        (1 - (maxEnt (con.comap (x, ·)).violations w).real {a} -
          (maxEnt (con.comap (x, ·)).violations w).real {b}) /
          (maxEnt (con.comap (x, ·)).violations w).real {b}).sum := by
  have : Nonempty Y := ⟨a⟩
  refine abs_interaction_logit_le (fun x ↦ maxEnt_real_singleton_pos _ w a)
    (fun x ↦ maxEnt_real_singleton_pos _ w b) (fun x ↦ ?_) (h.interaction_logOdds_maxEnt w)
  rw [← Finset.sum_pair (f := fun c ↦ (maxEnt (con.comap (x, ·)).violations w).real {c}) hab,
    ← sum_measureReal_singleton_eq_one (maxEnt (con.comap (x, ·)).violations w)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ ↦ measureReal_nonneg

/-- MaxEnt predicts HZ's generalization ((22) of [magri-2025]): when the two variants are the
only candidates, the MaxEnt logit rates have zero interaction, for every weighting. -/
theorem Independent.interaction_logit_maxEnt [Fintype Y] [DecidableEq Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] {con : ConstraintSet (X × Y) (Fin n)} {a b : Y}
    (h : sq.Independent con a b) (hab : a ≠ b) (hY : (Finset.univ : Finset Y) = {a, b})
    (w : Fin n → ℝ) :
    sq.interaction (fun x ↦ log ((maxEnt (con.comap (x, ·)).violations w).real {a} /
      (1 - (maxEnt (con.comap (x, ·)).violations w).real {a}))) = 0 := by
  have : Nonempty Y := ⟨a⟩
  have hsum (x : X) : 1 - (maxEnt (con.comap (x, ·)).violations w).real {a} -
      (maxEnt (con.comap (x, ·)).violations w).real {b} = 0 := by
    rw [← sum_measureReal_singleton_eq_one (maxEnt (con.comap (x, ·)).violations w), hY,
      Finset.sum_pair hab]
    ring
  simpa [hsum] using h.abs_interaction_logit_maxEnt_le hab w

end Square

end HarmonicGrammar
