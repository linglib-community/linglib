module

public import Linglib.Phonology.HarmonicGrammar.MaxEnt
public import Mathlib.LinearAlgebra.Pi

/-!
# Intersecting constraint families

Two constraint families *intersect* when each constraint is insensitive to one of two binary
factors: on the square of the four underlying forms crossing them, its violations of the two
surface variants are constant across the rows or across the columns. The *interaction contrast* is a
linear functional that vanishes [exactly when the differences along the two rows
agree](##HarmonicGrammar.Square.interaction_eq_zero_iff). Under independence [a sum of
per-constraint terms has zero
interaction](##HarmonicGrammar.Square.Independent.interaction_sum_eq_zero), and so do [the MaxEnt
log-odds of the two variants](##HarmonicGrammar.Square.Independent.interaction_logOdds_maxEnt).

## Main definitions

* `HarmonicGrammar.Square`: four underlying forms crossing two binary factors, (12) of
  [magri-2025].
* `Square.interaction`: the interaction contrast `f tl - f tr - f bl + f br`, and `Square.sum`,
  the sum over the four forms; both linear functionals on the functions of the forms.
* `Square.InsensitiveToRow`, `Square.InsensitiveToCol`, `Square.Independent`: the independence
  of the rows and columns relative to a constraint set, on two surface variants.

## References

* [zuraw-hayes-2017]
* [hayes-2022]
* [magri-2025]
-/

@[expose] public section

namespace HarmonicGrammar

open Real OptimalityTheory

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

variable (sq) in
/-- The sum of `f` over the four forms. -/
def sum : (X → R) →ₗ[R] R :=
  .proj sq.tl + .proj sq.tr + .proj sq.bl + .proj sq.br

@[simp] theorem sum_apply (f : X → R) : sq.sum f = f sq.tl + f sq.tr + f sq.bl + f sq.br :=
  rfl

section Order

variable [LinearOrder R] [IsStrictOrderedRing R]

theorem sum_le_sum {f g : X → R} (h : ∀ x, f x ≤ g x) : sq.sum f ≤ sq.sum g := by
  simp only [sum_apply]
  linarith [h sq.tl, h sq.tr, h sq.bl, h sq.br]

/-- The interaction of a nonnegative function is at most its sum over the four forms. -/
theorem abs_interaction_le_sum {f : X → R} (hf : ∀ x, 0 ≤ f x) :
    |sq.interaction f| ≤ sq.sum f := by
  rw [interaction_apply, sum_apply, abs_le]
  constructor <;> linarith [hf sq.tl, hf sq.tr, hf sq.bl, hf sq.br]

end Order

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

end Square

end HarmonicGrammar
