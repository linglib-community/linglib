module

public import Linglib.Phonology.HarmonicGrammar.MaxEnt
public import Mathlib.LinearAlgebra.Pi

/-!
# Intersecting constraint families

Two constraint families intersect ([zuraw-hayes-2017]) when a variable process is conditioned by
two binary factors and each constraint is sensitive to at most one of them: arranging the four
underlying forms that cross the factors into a square, each constraint is insensitive to the rows
or to the columns, at every candidate (§2.4 of [magri-2025]). [zuraw-hayes-2017] and
[hayes-2022] observe that the rates of application to the four forms then fit two shifted
sigmoids at shared abscissas. [magri-2025] restates the generalization on logit rates: the
difference between the logit rates of two forms in one row does not depend on the row (13).
Equivalently, the interaction contrast of the logit rates on the square vanishes; this file
states the generalization so, as the kernel of a linear functional.

A function of a form's violations that is a sum of per-constraint terms has zero interaction
whenever the families intersect, since each term is insensitive to one dimension. The MaxEnt
log-odds of two candidates is such a sum, the weighted violation differences, so MaxEnt predicts
the generalization for every weighting and every candidate set.

## Main definitions

* `HarmonicGrammar.Square`: four underlying forms crossing two binary factors, (12) of
  [magri-2025].
* `Square.interaction`: the interaction contrast `f tl - f tr - f bl + f br`, a linear
  functional on the functions of the forms.
* `Square.InsensitiveToRow`, `Square.InsensitiveToCol`, `Square.Independent`: the independence
  of the rows and columns relative to a constraint set.

## Main results

* `Square.Independent.interaction_sum_eq_zero`: under independence, a sum of per-constraint terms
  has zero interaction.
* `Square.Independent.interaction_logOdds_maxEnt`: MaxEnt predicts the generalization, (22) of
  [magri-2025].

## References

* [zuraw-hayes-2017]
* [hayes-2022]
* [magri-2025]
-/

@[expose] public section

namespace HarmonicGrammar

open Real OptimalityTheory Function

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

/-- The rows and columns are independent dimensions relative to `con` (§2.4 of [magri-2025]):
each constraint is insensitive to the rows or to the columns, reading its violations of all the
candidates of a form at once. -/
def Independent (con : ConstraintSet (X × Y) (Fin n)) : Prop :=
  ∀ k, sq.InsensitiveToRow (curry (con k)) ∨ sq.InsensitiveToCol (curry (con k))

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
violations of the candidates of a form, has zero interaction. -/
theorem Independent.interaction_sum_eq_zero {con : ConstraintSet (X × Y) (Fin n)}
    (h : sq.Independent con)
    (φ : Fin n → (Y → ℕ) → R) : sq.interaction (fun x ↦ ∑ k, φ k (curry (con k) x)) = 0 := by
  rw [show (fun x ↦ ∑ k, φ k (curry (con k) x)) = ∑ k, φ k ∘ curry (con k) by ext; simp,
    map_sum]
  exact Finset.sum_eq_zero fun k _ ↦ (h k).elim (·.comp _ |>.interaction_eq_zero)
    (·.comp _ |>.interaction_eq_zero)

theorem Independent.interaction_harmonyScore_sub {con : ConstraintSet (X × Y) (Fin n)}
    (h : sq.Independent con) (w : Fin n → R) (a b : Y) :
    sq.interaction (fun x ↦ harmonyScore con w (x, a) - harmonyScore con w (x, b)) = 0 := by
  convert h.interaction_sum_eq_zero (fun k v ↦ w k * v b - w k * v a) using 2
  ext x
  simp only [harmonyScore_eq_neg_sum, curry_apply, Finset.sum_sub_distrib]
  ring

end Interaction

/-- MaxEnt predicts HZ's generalization ((22) of [magri-2025]): under independence, the MaxEnt
log-odds of two candidates have zero interaction, for every weighting and every candidate set. -/
theorem Independent.interaction_logOdds_maxEnt [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] {con : ConstraintSet (X × Y) (Fin n)} (h : sq.Independent con)
    (w : Fin n → ℝ) (a b : Y) :
    sq.interaction (fun x ↦ log ((maxEnt (con.comap (x, ·)).violations w).real {a} /
      (maxEnt (con.comap (x, ·)).violations w).real {b})) = 0 := by
  simpa only [log_maxEnt_real_singleton_div, harmony_violations, harmonyScore_comap] using
    h.interaction_harmonyScore_sub w a b

end Square

end HarmonicGrammar
