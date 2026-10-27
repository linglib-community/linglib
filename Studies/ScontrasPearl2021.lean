module

public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Core.Probability.Kernel.Basic
public import Linglib.Pragmatics.RSA.Uniform
public import Linglib.Semantics.Quantification.NumberTree
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Core.Probability.Distributions.Binomial
public import Linglib.Core.Probability.Kernel.Posterior

/-!
# Scontras and Pearl (2021): When Pragmatics Matters More for Truth-Value Judgments

Scontras and Pearl model the truth-value judgment task for the scopally ambiguous sentences
*every horse didn't jump* and *two horses didn't jump*. A world is the number of horses that
jumped. A speaker who knows the world, a scope interpretation and a question under discussion
chooses between the sentence and silence, aiming to convey the answer to the question (`S1`). A
pragmatic listener inverts that speaker jointly over worlds, interpretations and questions
(`L1`). The endorsing speaker, who sees only the world, chooses between the sentence and silence
by the listener's beliefs about the world (`S2`), so that a truth-value judgment is a production
decision.

## Main results

* `one_half_lt_S2_real_amb_iff`: the sentence is endorsed more often than not exactly when it is
  produced at the observed world more often than on average.
* `S2_real_amb_all`: once the question is whether all the horses jumped, the two interpretations
  of *every horse didn't jump* produce alike and the scope prior does not affect endorsement.
* `S2_real_amb_mono_baseRate`: production falls with the number of jumpers, so a higher success
  base rate in the binomial world prior raises endorsement.
* `share_twoAtLeast_le_share_twoExact`, `share_twoExact_lt_share_twoAtLeast`: with four horses
  and two jumpers the surface speaker favors the exact reading whatever the question, while the
  inverse speaker asked whether all jumped favors the at-least reading.

## Implementation notes

* The rationality of `S1` and the priors on worlds, interpretations and questions are
  parameters.
* A determiner is a quantifier on van Benthem's tree of numbers, a relation between the number
  of restrictor members outside its scope and the number inside it. *Every* is `NumberTree.all`,
  a numeral is the cardinal quantifier of the interval of a `Degree.Comparison`, and a scope
  interpretation is a negation of the determiner (`Scope.negation`), inner for surface scope and
  outer for inverse scope. The paper tabulates the truth conditions at two and at four horses,
  and here they follow for any number.
* Both models share the paper's five questions. The every-not model is the case of a question
  prior carried by the first three.
* Utterances are costless and the literal listener carries no world prior, following Qing and
  Franke. The speaker addresses the question as in the hyperbole model of Kao and colleagues.

## TODO

* The numerical predictions of the paper's figures, at unit rationality and its grid of priors,
  are not stated.
* The base-rate result is proved at two horses, the paper's scenario. For any number of horses
  it would follow from `production` being antitone and the binomial family being stochastically
  increasing in its success probability.

## References

* [scontras-pearl-2021]
* [musolino-lidz-2003]
* [kao-etal-2014-hyperbole]
* [qing-franke-2015]
* [goodman-frank-2016]
* [van-benthem-1984]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA Quantifier
open scoped ENNReal unitInterval Fin.NatCast

namespace ScontrasPearl2021

/-- The utterances of (2) are the null utterance, which says nothing, and the scopally ambiguous
test sentence. -/
inductive Utt
  | null | amb
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utt := ⊤
instance : DiscreteMeasurableSpace Utt := ⟨fun _ ↦ trivial⟩

/-- The scope interpretations of the test sentence put the determiner over negation, or negation
over the determiner. -/
inductive Scope
  | surface | inverse
  deriving DecidableEq, Fintype

instance : MeasurableSpace Scope := ⊤
instance : DiscreteMeasurableSpace Scope := ⟨fun _ ↦ trivial⟩
instance : Nonempty Scope := ⟨.surface⟩

/-- The questions under discussion of (3) and (7) ask how many horses jumped, and whether all,
none, exactly two or at least two did. -/
inductive QUD
  | howMany | all | none | exactlyTwo | atLeastTwo
  deriving DecidableEq, Fintype

instance : MeasurableSpace QUD := ⊤
instance : DiscreteMeasurableSpace QUD := ⟨fun _ ↦ trivial⟩
instance : Nonempty QUD := ⟨.howMany⟩

/-- A world is the number of horses, out of `n`, that jumped. -/
abbrev World (n : ℕ) := Fin (n + 1)

/-! ### Semantics -/

/-- A scope interpretation negates the determiner on the tree of numbers. The surface
interpretation, the determiner over negation, is its inner negation, and the inverse
interpretation, negation over the determiner, is its outer negation. -/
def Scope.negation : Scope → NumberTree → NumberTree
  | .surface, D => D.innerNeg
  | .inverse, D => Dᶜ

instance (i : Scope) (D : NumberTree) [DecidableRel D] : DecidableRel (i.negation D) :=
  match i with
  | .surface => inferInstanceAs (DecidableRel D.innerNeg)
  | .inverse => inferInstanceAs (DecidableRel Dᶜ)

theorem negation_surface_all : Scope.surface.negation NumberTree.all = NumberTree.no := rfl

theorem negation_inverse_all : Scope.inverse.negation NumberTree.all = NumberTree.notAll := rfl

/-- A numeral is the cardinal quantifier of the interval that the comparison `c` selects at `k`.
The comparison `.eq` gives the exact reading and `.ge` the at-least reading. -/
def numeral (c : Degree.Comparison) (k : ℕ) : NumberTree := .cardinal (c.interval k)

instance (c : Degree.Comparison) (k : ℕ) : DecidableRel (numeral c k) :=
  inferInstanceAs (DecidableRel (NumberTree.cardinal (c.interval k)))

/-- The numeral *two* on its exact reading. -/
abbrev twoExact : NumberTree := numeral .eq 2

/-- The numeral *two* on its at-least reading. -/
abbrev twoAtLeast : NumberTree := numeral .ge 2

/-- The extension of an utterance under a scope interpretation ((2), (6)) among `n` horses. The
null utterance is true everywhere. With `w` jumpers, `n - w` horses lie outside the scope *jump*
and `w` inside it, and *D horses didn't jump* is true when the interpretation's negation of `D`
holds of those two counts. -/
def ext (D : NumberTree) [DecidableRel D] (n : ℕ) : Scope → Utt → Finset (World n)
  | _, .null => Finset.univ
  | i, .amb => (i.negation D).row n

section Ext

variable {D : NumberTree} [DecidableRel D] {c : Degree.Comparison} {k n : ℕ} {w : World n}

theorem mem_ext {i : Scope} : w ∈ ext D n i .amb ↔ i.negation D (n - w) w := by simp [ext]

theorem mem_ext_surface : w ∈ ext D n .surface .amb ↔ D w (n - w) := mem_ext

theorem mem_ext_inverse : w ∈ ext D n .inverse .amb ↔ ¬ D (n - w) w := mem_ext

-- (2)
theorem mem_ext_every_surface : w ∈ ext NumberTree.all n .surface .amb ↔ w = 0 := by
  simp only [mem_ext_surface, NumberTree.all, Fin.ext_iff, Fin.val_zero]

-- (2)
theorem mem_ext_every_inverse : w ∈ ext NumberTree.all n .inverse .amb ↔ w ≠ Fin.last n := by
  simp only [mem_ext_inverse, NumberTree.all, Ne, Fin.ext_iff, Fin.val_last]
  omega

-- (6)
theorem mem_ext_numeral_surface :
    w ∈ ext (numeral c k) n .surface .amb ↔ c.Rel (n - w) k := by
  simp only [mem_ext_surface, numeral, NumberTree.cardinal_apply, Degree.Comparison.mem_interval]

-- (6)
theorem mem_ext_numeral_inverse :
    w ∈ ext (numeral c k) n .inverse .amb ↔ ¬ c.Rel (w : ℕ) k := by
  simp only [mem_ext_inverse, numeral, NumberTree.cardinal_apply, Degree.Comparison.mem_interval]

theorem ext_congr {D' : NumberTree} [DecidableRel D']
    (h : ∀ a b, a + b = n → (D a b ↔ D' a b)) (i : Scope) (u : Utt) :
    ext D n i u = ext D' n i u := by
  cases u
  · rfl
  · ext w
    cases i
    · rw [mem_ext_surface, mem_ext_surface, h _ _ (Nat.add_sub_of_le w.is_le)]
    · rw [mem_ext_inverse, mem_ext_inverse, h _ _ (Nat.sub_add_cancel w.is_le)]

theorem numeral_eq_iff_all {a b : ℕ} (h : a + b = n) :
    numeral .eq n a b ↔ NumberTree.all a b := by
  simp only [numeral, NumberTree.cardinal_apply, NumberTree.all, Degree.Comparison.mem_interval,
    Degree.Comparison.Rel]
  omega

theorem numeral_ge_iff_all {a b : ℕ} (h : a + b = n) :
    numeral .ge n a b ↔ NumberTree.all a b := by
  simp only [numeral, NumberTree.cardinal_apply, NumberTree.all, Degree.Comparison.mem_interval,
    Degree.Comparison.Rel]
  omega

-- §4.2.1
theorem ext_numeral_eq_self (n : ℕ) : ext (numeral .eq n) n = ext NumberTree.all n :=
  funext₂ <| ext_congr fun _ _ ↦ numeral_eq_iff_all

-- §4.2.1
theorem ext_numeral_ge_self (n : ℕ) : ext (numeral .ge n) n = ext NumberTree.all n :=
  funext₂ <| ext_congr fun _ _ ↦ numeral_ge_iff_all

end Ext

-- (6), Figure 5
theorem ext_twoExact_surface : ext twoExact 4 .surface .amb = {2} := by decide

-- (6)
theorem ext_twoExact_inverse : ext twoExact 4 .inverse .amb = {0, 1, 3, 4} := by decide

-- (6)
theorem ext_twoAtLeast_surface : ext twoAtLeast 4 .surface .amb = {0, 1, 2} := by decide

-- (6)
theorem ext_twoAtLeast_inverse : ext twoAtLeast 4 .inverse .amb = {0, 1} := by decide

/-- The projection of a question ((3), (7)) sends a world to its answer, the number of jumpers
for *how many?*, and for the polar questions whether all, none, exactly two or at least two
jumped. -/
def project (n : ℕ) : QUD → World n → World n ⊕ Bool
  | .howMany, w => .inl w
  | .all, w => .inr (decide (w = Fin.last n))
  | .none, w => .inr (decide (w = 0))
  | .exactlyTwo, w => .inr (decide ((w : ℕ) = 2))
  | .atLeastTwo, w => .inr (decide (2 ≤ (w : ℕ)))

/-- The cell of a world under a question is the set of worlds sharing its answer. -/
def cell (n : ℕ) (q : QUD) (w : World n) : Finset (World n) :=
  Finset.univ.filter fun w' ↦ project n q w' = project n q w

theorem mem_cell {n : ℕ} {q : QUD} {w w' : World n} :
    w' ∈ cell n q w ↔ project n q w' = project n q w := by
  simp [cell]

theorem mem_cell_self {n : ℕ} (q : QUD) (w : World n) : w ∈ cell n q w := mem_cell.mpr rfl

theorem mem_cell_all {n : ℕ} {w w' : World n} :
    w' ∈ cell n .all w ↔ (w' = Fin.last n ↔ w = Fin.last n) := by
  simp [mem_cell, project]

theorem cell_exactlyTwo_two (w : World 2) : cell 2 .exactlyTwo w = cell 2 .all w := by
  revert w; decide

theorem cell_atLeastTwo_two (w : World 2) : cell 2 .atLeastTwo w = cell 2 .all w := by
  revert w; decide

/-! ### The model -/

section Model

variable (D : NumberTree) [DecidableRel D] (n : ℕ)

/-- The literal listener is uniform on the extension of the utterance under the scope
interpretation, with no world prior (fn. 6). -/
noncomputable def L0 (i : Scope) : Kernel Utt (World n) :=
  listener (uniformOn Set.univ) (truthful fun u ↦ (↑(ext D n i u) : Set (World n)))

instance (i : Scope) : IsFiniteKernel (L0 D n i) :=
  inferInstanceAs (IsFiniteKernel (listener _ (truthful _)))

theorem map_L0_apply (i : Scope) (q : QUD) (u : Utt) (w : World n) :
    (L0 D n i).map (project n q) u {project n q w}
      = uniformOn ↑(ext D n i u) (↑(cell n q w) : Set (World n)) := by
  rw [Kernel.map_apply_singleton, L0, listener_uniformOn_truthful_apply]
  congr 1
  ext w'
  simp [cell]

variable (α : ℝ)

/-- The speaker of §3.1, at a world, a scope interpretation and a question, knows the world's
answer to the question and is informative at rationality `α` about the belief of the
interpretation's literal listener about it. The utterances are costless (fn. 8). -/
noncomputable def S1 : Kernel (World n × (Scope × QUD)) Utt :=
  Kernel.ofFunOfCountable fun p ↦
    speaker α 0 ((L0 D n p.2.1).map (project n p.2.2)) Measure.dirac (project n p.2.2 p.1)

theorem S1_apply (w : World n) (l : Scope × QUD) :
    S1 D n α (w, l) =
      speaker α 0 ((L0 D n l.1).map (project n l.2)) Measure.dirac (project n l.2 w) := rfl

instance : IsFiniteKernel (S1 D n α) :=
  ⟨⟨1, ENNReal.one_lt_top, fun p ↦ speaker_apply_univ_le_one α 0
    ((L0 D n p.2.1).map (project n p.2.2)) Measure.dirac (project n p.2.2 p.1)⟩⟩

theorem isMarkovKernel_S1 (hα : 0 ≤ α) : IsMarkovKernel (S1 D n α) := by
  refine ⟨fun p ↦ ?_⟩
  obtain ⟨w, l⟩ := p
  rw [S1_apply]
  exact isProbabilityMeasure_speaker_dirac hα 0 _ ⟨.null, by
    rw [map_L0_apply, Ne, uniformOn_eq_zero_iff (Finset.finite_toSet _)]
    exact Set.nonempty_iff_ne_empty.mp
      ⟨w, Finset.mem_coe.mpr (Finset.mem_univ w), Finset.mem_coe.mpr (mem_cell_self l.2 w)⟩⟩

variable (μ : Measure (World n)) (ν : Measure (Scope × QUD))

/-- The pragmatic listener of §3.1 inverts the speaker over worlds, interpretations and
questions, against the product of the world prior and a prior on interpretations and questions
(the paper's `P(i) P(q)`). -/
noncomputable def L1 : Kernel Utt (World n × (Scope × QUD)) :=
  listener (μ.prod ν) (S1 D n α)

instance : IsFiniteKernel (L1 D n α μ ν) := inferInstanceAs (IsFiniteKernel (listener _ _))

/-- The endorsing speaker of §3.1 is, at the observed world, the best response at unit rationality
to the world marginal of the pragmatic listener. -/
noncomputable def S2 : Kernel (World n) Utt := speaker 1 0 (Kernel.fst (L1 D n α μ ν)) Measure.dirac

-- §4.2.1
theorem S2_numeral_eq_self : S2 (numeral .eq n) n α μ ν = S2 NumberTree.all n α μ ν := by
  simp only [S2, L1, S1, L0, ext_numeral_eq_self]

-- §4.2.1
theorem S2_numeral_ge_self : S2 (numeral .ge n) n α μ ν = S2 NumberTree.all n α μ ν := by
  simp only [S2, L1, S1, L0, ext_numeral_ge_self]

end Model

/-! ### Production shares -/

section Share

variable (D : NumberTree) [DecidableRel D] (n : ℕ) (α : ℝ)

/-- The cell mass is the fraction of the extension of an utterance under a scope interpretation
that lies in the cell of a world under a question, which is the literal listener's mass on the
world's answer. -/
noncomputable def cellMass (l : Scope × QUD) (u : Utt) (w : World n) : ℝ :=
  ((L0 D n l.1).map (project n l.2) u).real {project n l.2 w}

theorem cellMass_eq (l : Scope × QUD) (u : Utt) (w : World n) :
    cellMass D n l u w = ((ext D n l.1 u ∩ cell n l.2 w).card : ℝ) / (ext D n l.1 u).card := by
  rw [cellMass, measureReal_def, map_L0_apply, uniformOn_apply_finset, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]

theorem cellMass_nonneg (l : Scope × QUD) (u : Utt) (w : World n) : 0 ≤ cellMass D n l u w :=
  measureReal_nonneg

theorem cellMass_null_pos (l : Scope × QUD) (w : World n) : 0 < cellMass D n l .null w := by
  rw [cellMass_eq]
  refine div_pos ?_ (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨w, Finset.mem_univ w⟩))
  exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr
    ⟨Finset.mem_univ w, mem_cell_self l.2 w⟩⟩)

/-- The share is the probability that the speaker produces the test sentence at a world under a
scope interpretation and a question. -/
noncomputable def share (l : Scope × QUD) (w : World n) : ℝ := (S1 D n α (w, l)).real {.amb}

private theorem sum_utt (f : Utt → ℝ) : ∑ u, f u = f .amb + f .null :=
  Fintype.sum_eq_add Utt.amb Utt.null (by decide) (fun u h ↦ by cases u <;> simp at h)

theorem share_eq (hα : 0 ≤ α) (l : Scope × QUD) (w : World n) :
    share D n α l w
      = cellMass D n l .amb w ^ α / (cellMass D n l .amb w ^ α + cellMass D n l .null w ^ α) := by
  rw [share, S1_apply, speaker_dirac_zero_real_singleton hα, sum_utt]
  simp only [cellMass, measureReal_def, ENNReal.toReal_rpow]

theorem share_nonneg (l : Scope × QUD) (w : World n) : 0 ≤ share D n α l w := measureReal_nonneg

theorem share_le_one (l : Scope × QUD) (w : World n) : share D n α l w ≤ 1 := by
  rw [share, S1_apply]
  exact speaker_real_singleton_le_one _ _ _ _ _ _

theorem share_lt_one (hα : 0 ≤ α) (l : Scope × QUD) (w : World n) : share D n α l w < 1 := by
  rw [share_eq D n α hα]
  have hy := Real.rpow_pos_of_pos (cellMass_null_pos D n l w) α
  have hx := Real.rpow_nonneg (cellMass_nonneg D n l .amb w) α
  rw [div_lt_one (add_pos_of_nonneg_of_pos hx hy)]
  linarith

theorem share_pos (hα : 0 ≤ α) {l : Scope × QUD} {w : World n} (h : w ∈ ext D n l.1 .amb) :
    0 < share D n α l w := by
  rw [share_eq D n α hα]
  have hy := Real.rpow_pos_of_pos (cellMass_null_pos D n l w) α
  refine div_pos (Real.rpow_pos_of_pos ?_ α)
    (add_pos_of_nonneg_of_pos (Real.rpow_nonneg (cellMass_nonneg _ _ _ _ _) α) hy)
  rw [cellMass_eq]
  refine div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr
    ⟨h, mem_cell_self l.2 w⟩⟩)) (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨w, h⟩))

theorem S1_real_null (hα : 0 ≤ α) (l : Scope × QUD) (w : World n) :
    (S1 D n α (w, l)).real {.null} = 1 - share D n α l w := by
  have := isMarkovKernel_S1 D n α hα
  have h := probReal_univ (μ := S1 D n α (w, l))
  rw [← Finset.coe_univ, ← sum_measureReal_singleton, sum_utt] at h
  rw [share]
  linarith

/-- The cell count is the number of worlds in the cell of `w` under the question of `l` at which
`u` is true under the interpretation of `l`. -/
def cellCount (l : Scope × QUD) (u : Utt) (w : World n) : ℕ := (ext D n l.1 u ∩ cell n l.2 w).card

private theorem cellMass_mul_cellMass_le_iff {D' : NumberTree} [DecidableRel D']
    {l l' : Scope × QUD} {w w' : World n} (hS : 0 < (ext D n l.1 .amb).card)
    (hS' : 0 < (ext D' n l'.1 .amb).card) :
    cellMass D n l .amb w * cellMass D' n l' .null w'
        ≤ cellMass D' n l' .amb w' * cellMass D n l .null w
      ↔ cellCount D n l .amb w * cellCount D' n l' .null w' * (ext D' n l'.1 .amb).card
        ≤ cellCount D' n l' .amb w' * cellCount D n l .null w * (ext D n l.1 .amb).card := by
  simp only [cellMass_eq, cellCount]
  have hN : (0 : ℝ) < (ext D' n l'.1 .null).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨w', Finset.mem_univ _⟩)
  have hN' : (ext D n l.1 .null).card = (ext D' n l'.1 .null).card := rfl
  rw [hN', div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff₀ (by positivity) (by positivity), ← mul_assoc, ← mul_assoc]
  exact ⟨fun h ↦ by exact_mod_cast le_of_mul_le_mul_right h hN,
    fun h ↦ mul_le_mul_of_nonneg_right (by exact_mod_cast h) hN.le⟩

theorem share_le_share_iff (hα : 0 < α) {D' : NumberTree} [DecidableRel D']
    {l l' : Scope × QUD} {w w' : World n} (hS : 0 < (ext D n l.1 .amb).card)
    (hS' : 0 < (ext D' n l'.1 .amb).card) :
    share D n α l w ≤ share D' n α l' w'
      ↔ cellCount D n l .amb w * cellCount D' n l' .null w' * (ext D' n l'.1 .amb).card
        ≤ cellCount D' n l' .amb w' * cellCount D n l .null w * (ext D n l.1 .amb).card := by
  rw [share_eq D n α hα.le, share_eq D' n α hα.le, ← cellMass_mul_cellMass_le_iff D n hS hS']
  have hx := Real.rpow_nonneg (cellMass_nonneg D n l .amb w) α
  have hx' := Real.rpow_nonneg (cellMass_nonneg D' n l' .amb w') α
  have hy := Real.rpow_pos_of_pos (cellMass_null_pos D n l w) α
  have hy' := Real.rpow_pos_of_pos (cellMass_null_pos D' n l' w') α
  rw [div_le_div_iff₀ (by linarith) (by linarith), ← Real.rpow_le_rpow_iff (z := α)
    (mul_nonneg (cellMass_nonneg _ _ _ _ _) (cellMass_nonneg _ _ _ _ _))
    (mul_nonneg (cellMass_nonneg _ _ _ _ _) (cellMass_nonneg _ _ _ _ _)) hα,
    Real.mul_rpow (cellMass_nonneg _ _ _ _ _) (cellMass_nonneg _ _ _ _ _),
    Real.mul_rpow (cellMass_nonneg _ _ _ _ _) (cellMass_nonneg _ _ _ _ _)]
  constructor <;> intro h <;> nlinarith

theorem share_lt_share_iff (hα : 0 < α) {D' : NumberTree} [DecidableRel D']
    {l l' : Scope × QUD} {w w' : World n} (hS : 0 < (ext D n l.1 .amb).card)
    (hS' : 0 < (ext D' n l'.1 .amb).card) :
    share D n α l w < share D' n α l' w'
      ↔ cellCount D n l .amb w * cellCount D' n l' .null w' * (ext D' n l'.1 .amb).card
        < cellCount D' n l' .amb w' * cellCount D n l .null w * (ext D n l.1 .amb).card := by
  rw [← not_le, share_le_share_iff D' n α hα hS' hS, not_le]

end Share

/-! ### Endorsement -/

section Endorsement

variable (D : NumberTree) [DecidableRel D] (n : ℕ) (α : ℝ) (μ : Measure (World n))
  (ν : Measure (Scope × QUD))

/-- The production at a world is the probability that the test sentence is produced there, the
interpretation and the question drawn from `ν`. -/
noncomputable def production (w : World n) : ℝ := ∑ l, ν.real {l} * share D n α l w

/-- The expected production is the prior probability that the test sentence is produced, the
observation marginal of the speaker. -/
noncomputable def expectedProduction : ℝ := (S1 D n α ∘ₘ μ.prod ν).real {.amb}

theorem production_nonneg (w : World n) : 0 ≤ production D n α ν w :=
  Finset.sum_nonneg fun l _ ↦ mul_nonneg measureReal_nonneg (share_nonneg D n α l w)

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem expectedProduction_eq_sum :
    expectedProduction D n α μ ν = ∑ w, μ.real {w} * production D n α ν w := by
  rw [expectedProduction, Measure.comp_real_singleton, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [production, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [Measure.prod_real_singleton, share, mul_assoc]

theorem production_le_one (w : World n) : production D n α ν w ≤ 1 :=
  (Finset.sum_le_sum fun l _ ↦
    mul_le_of_le_one_right measureReal_nonneg (share_le_one D n α l w)).trans_eq
    (sum_measureReal_singleton_eq_one ν)

theorem production_lt_one (hα : 0 ≤ α) (w : World n) : production D n α ν w < 1 := by
  obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    ((sum_measureReal_singleton_eq_one ν).trans_ne one_ne_zero)
  refine (Finset.sum_lt_sum (fun l _ ↦ mul_le_of_le_one_right measureReal_nonneg
    (share_le_one D n α l w)) ⟨l, Finset.mem_univ l, ?_⟩).trans_eq
    (sum_measureReal_singleton_eq_one ν)
  exact mul_lt_of_lt_one_right (lt_of_le_of_ne measureReal_nonneg (Ne.symm hl))
    (share_lt_one D n α hα l w)

theorem production_pos (hα : 0 ≤ α) {w : World n} (h : ∀ l : Scope × QUD, w ∈ ext D n l.1 .amb) :
    0 < production D n α ν w := by
  obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    ((sum_measureReal_singleton_eq_one ν).trans_ne one_ne_zero)
  exact Finset.sum_pos' (fun l _ ↦ mul_nonneg measureReal_nonneg (share_nonneg D n α l w))
    ⟨l, Finset.mem_univ l, mul_pos (lt_of_le_of_ne measureReal_nonneg (Ne.symm hl))
      (share_pos D n α hα (h l))⟩

theorem expectedProduction_lt_one (hα : 0 ≤ α) : expectedProduction D n α μ ν < 1 := by
  rw [expectedProduction_eq_sum]
  obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    ((sum_measureReal_singleton_eq_one μ).trans_ne one_ne_zero)
  refine (Finset.sum_lt_sum (fun w _ ↦ mul_le_of_le_one_right measureReal_nonneg
    (production_le_one D n α ν w)) ⟨w, Finset.mem_univ w, ?_⟩).trans_eq
    (sum_measureReal_singleton_eq_one μ)
  exact mul_lt_of_lt_one_right (lt_of_le_of_ne measureReal_nonneg (Ne.symm hw))
    (production_lt_one D n α ν hα w)

theorem expectedProduction_pos (hα : 0 ≤ α) {w : World n} (hμ : μ {w} ≠ 0)
    (h : ∀ l : Scope × QUD, w ∈ ext D n l.1 .amb) : 0 < expectedProduction D n α μ ν := by
  rw [expectedProduction_eq_sum]
  exact Finset.sum_pos' (fun w _ ↦ mul_nonneg measureReal_nonneg (production_nonneg D n α ν w))
    ⟨w, Finset.mem_univ w, mul_pos (ENNReal.toReal_pos hμ (measure_ne_top _ _))
      (production_pos D n α ν hα h)⟩

/-- `endorse m z` is the endorsement probability as a function of the production probability `m`
at the observed world and its expectation `z` under the world prior. -/
noncomputable def endorse (m z : ℝ) : ℝ := m * (1 - z) / (m * (1 - z) + z * (1 - m))

section Endorse

variable {m m' z z' : ℝ}

theorem endorse_denom_pos (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) :
    0 < m * (1 - z) + z * (1 - m) := by
  rcases hm1.lt_or_eq with hm | rfl
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hm0 (by linarith)) (mul_pos hz0 (by linarith))
  · rw [one_mul, sub_self, mul_zero, add_zero]
    linarith

theorem endorse_le_endorse (hm0 : 0 ≤ m) (hm1 : m' ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    (h : m ≤ m') : endorse m z ≤ endorse m' z := by
  unfold endorse
  rw [div_le_div_iff₀ (endorse_denom_pos hm0 (h.trans hm1) hz0 hz1)
    (endorse_denom_pos (hm0.trans h) hm1 hz0 hz1)]
  nlinarith [mul_nonneg (mul_nonneg hz0.le (sub_nonneg.2 hz1.le)) (sub_nonneg.2 h)]

theorem endorse_antitone (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hz0 : 0 < z) (hz1 : z' < 1)
    (h : z ≤ z') : endorse m z' ≤ endorse m z := by
  unfold endorse
  rw [div_le_div_iff₀ (endorse_denom_pos hm0 hm1 (hz0.trans_le h) hz1)
    (endorse_denom_pos hm0 hm1 hz0 (h.trans_lt hz1))]
  nlinarith [mul_nonneg (mul_nonneg hm0 (sub_nonneg.2 hm1)) (sub_nonneg.2 h)]

theorem one_half_lt_endorse_iff (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) :
    1 / 2 < endorse m z ↔ z < m := by
  unfold endorse
  rw [div_lt_div_iff₀ two_pos (endorse_denom_pos hm0 hm1 hz0 hz1)]
  constructor <;> intro h <;> nlinarith

end Endorse

-- §3.1
theorem S2_real_amb (hα : 0 < α) {w : World n} (hμ : μ {w} ≠ 0)
    (hz0 : 0 < expectedProduction D n α μ ν) (hz1 : expectedProduction D n α μ ν < 1) :
    (S2 D n α μ ν w).real {.amb}
      = endorse (production D n α ν w) (expectedProduction D n α μ ν) := by
  have := isMarkovKernel_S1 D n α hα.le
  set m := production D n α ν w with hm
  set z := expectedProduction D n α μ ν with hz
  set a := μ.real {w} with ha
  have hZ : (S1 D n α ∘ₘ μ.prod ν).real {.null} = 1 - z := by
    have h := probReal_univ (μ := S1 D n α ∘ₘ μ.prod ν)
    rw [← Finset.coe_univ, ← sum_measureReal_singleton, sum_utt] at h
    have : (S1 D n α ∘ₘ μ.prod ν).real {.amb} = z := rfl
    linarith
  have hnull : ∑ l, ν.real {l} * (S1 D n α (w, l)).real {.null} = 1 - m := by
    simp only [S1_real_null D n α hα.le, mul_sub, mul_one, Finset.sum_sub_distrib,
      sum_measureReal_singleton_eq_one ν]
    rfl
  have hF (u : Utt) : (Kernel.fst (L1 D n α μ ν) u).real {w}
      = a * (∑ l, ν.real {l} * (S1 D n α (w, l)).real {u}) / (S1 D n α ∘ₘ μ.prod ν).real {u} := by
    rw [Measure.comp_real_singleton]
    exact listener_prod_fst_real_singleton μ ν _ u w
  have hFamb : (Kernel.fst (L1 D n α μ ν) .amb).real {w} = a * m / z := hF .amb
  have hFnull := hF .null
  rw [hnull, hZ] at hFnull
  rw [S2, speaker_dirac_zero_real_singleton zero_le_one]
  simp only [ENNReal.rpow_one, ← measureReal_def]
  rw [sum_utt, hFamb, hFnull, endorse]
  have ha0 : 0 < a := ENNReal.toReal_pos hμ (measure_ne_top _ _)
  have hm0 : 0 ≤ m := production_nonneg D n α ν w
  have hm1 : m ≤ 1 := production_le_one D n α ν w
  have hden := endorse_denom_pos hm0 hm1 hz0 hz1
  have hz0' : z ≠ 0 := hz0.ne'
  have h1z : 1 - z ≠ 0 := (sub_pos.2 hz1).ne'
  have hAB : 0 < a * m / z + a * (1 - m) / (1 - z) := by
    rcases hm0.lt_or_eq with hm | hm
    · exact add_pos_of_pos_of_nonneg (div_pos (mul_pos ha0 hm) hz0)
        (div_nonneg (mul_nonneg ha0.le (sub_nonneg.2 hm1)) (sub_pos.2 hz1).le)
    · rw [← hm, mul_zero, zero_div, zero_add, sub_zero, mul_one]
      exact div_pos ha0 (sub_pos.2 hz1)
  rw [div_eq_div_iff hAB.ne' hden.ne']
  field_simp

/-- The listener endorses the sentence more often than not iff its production at the observed world
exceeds its expected production under the prior (§5.1). -/
theorem one_half_lt_S2_real_amb_iff (hα : 0 < α) {w : World n} (hμ : μ {w} ≠ 0)
    (hz0 : 0 < expectedProduction D n α μ ν) (hz1 : expectedProduction D n α μ ν < 1) :
    1 / 2 < (S2 D n α μ ν w).real {.amb} ↔ expectedProduction D n α μ ν < production D n α ν w := by
  rw [S2_real_amb D n α μ ν hα hμ hz0 hz1,
    one_half_lt_endorse_iff (production_nonneg D n α ν w) (production_le_one D n α ν w) hz0 hz1]

end Endorsement

/-! ### The every-not model (§3) -/

section EveryNot

variable (α : ℝ) {n : ℕ}

private theorem zero_ne_last (hn : 0 < n) : (0 : World n) ≠ Fin.last n := fun h ↦
  hn.ne (by simpa [Fin.ext_iff] using h)

theorem zero_mem_ext_every (hn : 0 < n) (i : Scope) :
    (0 : World n) ∈ ext NumberTree.all n i .amb := by
  cases i
  · exact mem_ext_every_surface.mpr rfl
  · exact mem_ext_every_inverse.mpr (zero_ne_last hn)

theorem ext_every_amb_card_pos (hn : 0 < n) (i : Scope) : 0 < (ext NumberTree.all n i .amb).card :=
  Finset.card_pos.mpr ⟨0, zero_mem_ext_every hn i⟩

theorem map_L0_every_all (hn : 0 < n) (i : Scope) (w : World n) :
    (L0 NumberTree.all n i).map (project n .all) .amb {project n .all w}
      = if w = Fin.last n then 0 else 1 := by
  rw [map_L0_apply]
  have hcell : ∀ w', w' ∈ cell n .all w ↔ (w' = Fin.last n ↔ w = Fin.last n) := fun _ ↦ mem_cell_all
  have hext : ∀ w', w' ∈ ext NumberTree.all n i .amb → w' ≠ Fin.last n := fun w' h ↦ by
    cases i
    · exact (mem_ext_every_surface.mp h) ▸ zero_ne_last hn
    · exact mem_ext_every_inverse.mp h
  split_ifs with hw
  · rw [uniformOn_eq_zero_iff (Finset.finite_toSet _), Set.eq_empty_iff_forall_notMem]
    rintro w' ⟨h1, h2⟩
    exact hext w' (Finset.mem_coe.mp h1) (((hcell w').mp (Finset.mem_coe.mp h2)).mpr hw)
  · exact uniformOn_eq_one_of (Finset.finite_toSet _)
      ⟨0, Finset.mem_coe.mpr (zero_mem_ext_every hn i)⟩ fun w' h ↦
      Finset.mem_coe.mpr ((hcell w').mpr (iff_of_false (hext w' (Finset.mem_coe.mp h)) hw))

-- §3.2, §5.1
theorem S1_all_scope (hn : 0 < n) (w : World n) :
    S1 NumberTree.all n α (w, (.surface, .all)) = S1 NumberTree.all n α (w, (.inverse, .all)) := by
  rw [S1_apply, S1_apply, speaker_dirac_eq_ofWeights, speaker_dirac_eq_ofWeights]
  have key : ∀ u, (L0 NumberTree.all n .surface).map (project n .all) u {project n .all w}
      = (L0 NumberTree.all n .inverse).map (project n .all) u {project n .all w} := by
    intro u
    cases u
    · rw [map_L0_apply, map_L0_apply]
      rfl
    · rw [map_L0_every_all hn, map_L0_every_all hn]
  exact Measure.ext_of_singleton fun u ↦ by simp only [Kernel.ofWeights_apply_singleton, key]

theorem share_all_scope (hn : 0 < n) (w : World n) :
    share NumberTree.all n α (.surface, .all) w = share NumberTree.all n α (.inverse, .all) w := by
  simp only [share, S1_all_scope α hn w]

variable (ρ : Measure Scope) [IsProbabilityMeasure ρ]

theorem production_all (hn : 0 < n) (w : World n) :
    production NumberTree.all n α (ρ.prod (Measure.dirac .all)) w
      = share NumberTree.all n α (.surface, .all) w := by
  rw [production, Fintype.sum_prod_type]
  simp only [Measure.prod_real_singleton, Measure.dirac_real_apply, Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hscope : ∀ f : Scope → ℝ, ∑ i, f i = f .surface + f .inverse := fun f ↦
    Fintype.sum_eq_add Scope.surface Scope.inverse (by decide) (fun i h ↦ by cases i <;> simp at h)
  have hsum := sum_measureReal_singleton_eq_one ρ
  rw [hscope] at hsum
  rw [hscope, ← share_all_scope α hn w, ← add_mul, hsum, one_mul]

theorem expectedProduction_all (hn : 0 < n) (μ : Measure (World n)) [IsProbabilityMeasure μ] :
    expectedProduction NumberTree.all n α μ (ρ.prod (Measure.dirac .all))
      = ∑ w, μ.real {w} * share NumberTree.all n α (.surface, .all) w := by
  rw [expectedProduction_eq_sum]
  simp only [production_all α ρ hn]

/-- Under the question *all?*, endorsement does not depend on the scope prior (§3.2, Figure 3). -/
theorem S2_real_amb_all (hα : 0 < α) (hn : 0 < n) (μ : Measure (World n)) [IsProbabilityMeasure μ]
    (ρ' : Measure Scope) [IsProbabilityMeasure ρ'] {w : World n} (hμ : μ {w} ≠ 0)
    (hz0 : 0 < expectedProduction NumberTree.all n α μ (ρ.prod (Measure.dirac .all)))
    (hz1 : expectedProduction NumberTree.all n α μ (ρ.prod (Measure.dirac .all)) < 1) :
    (S2 NumberTree.all n α μ (ρ.prod (Measure.dirac .all)) w).real {.amb}
      = (S2 NumberTree.all n α μ (ρ'.prod (Measure.dirac .all)) w).real {.amb} := by
  have hz0' := hz0
  have hz1' := hz1
  rw [expectedProduction_all α ρ hn μ, ← expectedProduction_all α ρ' hn μ] at hz0' hz1'
  rw [S2_real_amb _ _ _ _ _ hα hμ hz0 hz1, S2_real_amb _ _ _ _ _ hα hμ hz0' hz1',
    production_all α ρ hn w, production_all α ρ' hn w, expectedProduction_all α ρ hn μ,
    expectedProduction_all α ρ' hn μ]

/-! #### Two horses (§3.2) -/

private theorem ext_every_two (l : Scope × QUD) : 0 < (ext NumberTree.all 2 l.1 .amb).card :=
  ext_every_amb_card_pos two_pos l.1

-- §3.2, Figure 2
theorem share_le_share_all (hα : 0 < α) (i : Scope) (q : QUD) :
    share NumberTree.all 2 α (i, q) 1 ≤ share NumberTree.all 2 α (i, .all) 1 :=
  (share_le_share_iff NumberTree.all 2 α hα (ext_every_two _) (ext_every_two _)).mpr
    (by revert i q; decide)

-- §3.2, Figure 2
theorem share_none_le_share (hα : 0 < α) (i : Scope) (q : QUD) :
    share NumberTree.all 2 α (i, .none) 1 ≤ share NumberTree.all 2 α (i, q) 1 :=
  (share_le_share_iff NumberTree.all 2 α hα (ext_every_two _) (ext_every_two _)).mpr
    (by revert i q; decide)

theorem share_howMany_lt_share_all (hα : 0 < α) :
    share NumberTree.all 2 α (.surface, .howMany) 1 < share NumberTree.all 2 α (.surface, .all) 1 :=
  (share_lt_share_iff NumberTree.all 2 α hα (ext_every_two _) (ext_every_two _)).mpr (by decide)

theorem share_none_lt_share_howMany (hα : 0 < α) :
    share NumberTree.all 2 α (.inverse, .none) 1
      < share NumberTree.all 2 α (.inverse, .howMany) 1 :=
  (share_lt_share_iff NumberTree.all 2 α hα (ext_every_two _) (ext_every_two _)).mpr (by decide)

theorem share_antitone (hα : 0 < α) (l : Scope × QUD) : Antitone (share NumberTree.all 2 α l) :=
  Fin.antitone_iff_succ_le.mpr <| Fin.forall_fin_two.mpr
    ⟨(share_le_share_iff NumberTree.all 2 α hα (ext_every_two _) (ext_every_two _)).mpr
        (by revert l; decide),
      (share_le_share_iff NumberTree.all 2 α hα (ext_every_two _) (ext_every_two _)).mpr
        (by revert l; decide)⟩

theorem production_antitone (hα : 0 < α) (ν : Measure (Scope × QUD)) :
    Antitone (production NumberTree.all 2 α ν) := fun _ _ h ↦
  Finset.sum_le_sum fun l _ ↦
    mul_le_mul_of_nonneg_left (share_antitone α hα l h) measureReal_nonneg

variable (ν : Measure (Scope × QUD)) [IsProbabilityMeasure ν]

/-- Raising the base rate of the binomial world prior raises endorsement at every world (§3.2,
Figure 2). -/
theorem S2_real_amb_mono_baseRate (hα : 0 < α) {p p' : I} (hp : 0 < (p : ℝ))
    (hpp' : (p : ℝ) ≤ p') (hp' : (p' : ℝ) < 1) (w : World 2) :
    (S2 NumberTree.all 2 α Bin(World 2, 2, p) ν w).real {.amb}
      ≤ (S2 NumberTree.all 2 α Bin(World 2, 2, p') ν w).real {.amb} := by
  have hpos : ∀ (q : I), 0 < (q : ℝ) → (q : ℝ) < 1 → ∀ w : World 2, Bin(World 2, 2, q) {w} ≠ 0 :=
    fun q hq hq1 w ↦ (measureReal_ne_zero_iff (measure_ne_top _ _)).mp (by
      rw [map_cast_binomial_fin_real_singleton]
      exact (mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos w.is_le)) (pow_pos hq _))
        (pow_pos (sub_pos.2 hq1) _)).ne')
  have hp1 : (p : ℝ) < 1 := hpp'.trans_lt hp'
  have hp'0 : 0 < (p' : ℝ) := hp.trans_le hpp'
  have hz0 : ∀ (q : I), 0 < (q : ℝ) → (q : ℝ) < 1 →
      0 < expectedProduction NumberTree.all 2 α Bin(World 2, 2, q) ν := fun q hq hq1 ↦
    expectedProduction_pos _ _ _ _ _ hα.le (hpos q hq hq1 0) fun l ↦ zero_mem_ext_every two_pos l.1
  rw [S2_real_amb _ _ _ _ _ hα (hpos p hp hp1 w) (hz0 p hp hp1)
      (expectedProduction_lt_one _ _ _ _ _ hα.le),
    S2_real_amb _ _ _ _ _ hα (hpos p' hp'0 hp' w) (hz0 p' hp'0 hp')
      (expectedProduction_lt_one _ _ _ _ _ hα.le)]
  refine endorse_antitone (production_nonneg _ _ _ _ _) (production_le_one _ _ _ _ _)
    (hz0 p' hp'0 hp') (expectedProduction_lt_one _ _ _ _ _ hα.le) ?_
  rw [expectedProduction_eq_sum, expectedProduction_eq_sum, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [map_cast_binomial_fin_real_singleton, Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, Nat.cast_one, Nat.cast_ofNat,
    pow_zero, Nat.sub_zero, Nat.sub_self, Nat.reduceSub, one_mul, mul_one, pow_one]
  have h10 := production_antitone α hα ν (show (0 : World 2) ≤ 1 by decide)
  have h21 := production_antitone α hα ν (show (1 : World 2) ≤ 2 by decide)
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hpp') (by linarith : (0 : ℝ) ≤ 2 - p - p'))
      (sub_nonneg.2 h10),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hpp') (by linarith : (0 : ℝ) ≤ p + p'))
      (sub_nonneg.2 h21)]

end EveryNot

/-! ### The two-not model (§4) -/

section TwoNot

variable (α : ℝ)

/-- With two of four horses jumping, the surface interpretation is produced at least as often on the
exact reading as on the at-least reading (§4.2.2, Figure 7). -/
theorem share_twoAtLeast_le_share_twoExact (hα : 0 < α) (q : QUD) :
    share twoAtLeast 4 α (.surface, q) 2 ≤ share twoExact 4 α (.surface, q) 2 :=
  (share_le_share_iff twoAtLeast 4 α hα
    (show 0 < (ext twoAtLeast 4 .surface .amb).card by decide)
    (show 0 < (ext twoExact 4 .surface .amb).card by decide)).mpr (by revert q; decide)

theorem share_twoAtLeast_lt_share_twoExact (hα : 0 < α) {q : QUD} (hq : q ≠ .all) :
    share twoAtLeast 4 α (.surface, q) 2 < share twoExact 4 α (.surface, q) 2 :=
  (share_lt_share_iff twoAtLeast 4 α hα
    (show 0 < (ext twoAtLeast 4 .surface .amb).card by decide)
    (show 0 < (ext twoExact 4 .surface .amb).card by decide)).mpr (by revert q hq; decide)

/-- With two of four horses jumping, under the inverse interpretation and the question *all?*, the
at-least reading is produced more often than the exact one (§4.2.2, Figure 7). -/
theorem share_twoExact_lt_share_twoAtLeast (hα : 0 < α) :
    share twoExact 4 α (.inverse, .all) 2 < share twoAtLeast 4 α (.inverse, .all) 2 :=
  (share_lt_share_iff twoExact 4 α hα (by decide) (by decide)).mpr (by decide)

end TwoNot

end ScontrasPearl2021
