module

public import Linglib.Phonology.HarmonicGrammar.MaxEnt
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Fin.VecNotation

/-!
# Breiss, Katsuda and Kawahara 2026: modelling frequency-conditioned paradigm uniformity

In conservative Japanese dialects a compound whose second member (N2) begins with /g/ realises it
as [ŋ], but only optionally when the N2 is also a free word, which begins with [g]. Nasalisation is
then more likely the more frequent the compound and less likely the more frequent the free N2.
Breiss, Katsuda and Kawahara derive both effects in a MaxEnt grammar under Breiss's Voting Bases
model, where a faithfulness violation counts in proportion to the resting activation of the listed
form it is assessed against. The free N2 is listed with [g] and an existing compound with [ŋ], so
the two effects take opposite signs.

The fitted grammar gives the markedness constraint against medial [g] no weight, against Itô and
Mester's markedness-driven account; activation raises faithfulness, where Coetzee and Kawahara let
frequency lower it; and the sign of each effect follows from the listed velars, where the earlier
output–output account of the same authors stipulated it.

## Main definitions

* `Item`: a compound's listed bases, an optional free N2 and an optional whole compound.
* `con`, `violations`, `votingBases`: the constraints (6), the violation vectors scaled by an
  item's activations, and the MaxEnt distribution of the item's realisations.
* `pNasal`: the probability of nasalisation.
* `table1`: the fitted weights.

## Main results

* `pNasal_eq_sigmoid`: the log-odds of nasalisation are the markedness weight plus each base's
  weighted activation, signed by its listed velar.
* `existing_strictAnti_n2`, `existing_strictMono_compound`, `novel_strictAnti_n2`: the frequency
  effects of Figures 2 and 3.
* `logit_pNasal_existing`: the N2 effect on the log-odds is the same in existing and novel
  compounds.
* `existing_lt_bound`: a free N2 lowers nasalisation below that of a bound N2.
* `table1_novel_lt_half`: under the fitted weights a novel compound nasalises less than half the
  time.
* `tableau7`, `tableau8`, `tableau9`: the schematic tableaux.

## Implementation notes

* A candidate is the realisation of the compound-medial velar, and identity in [nasal] to a base
  is one violation when the two velars differ.
* The tableaux display activation-scaled violations and the prose speaks of scaled weights;
  `harmony_violations_eq` shows the two agree. Scaling the violations keeps the weights the
  grammar's, shared across items, so the log-likelihood theory of `HarmonicGrammar.maxEnt`
  applies to the fit of Table 1.
* Tableau (8b) prints 0.91 for harmonies 2.7 and 0.5, which give σ(2.2) < 0.905
  (`pNasal_tableau8b_lt`).
* The caption of Table 1 describes weights fitted to existing and novel compounds combined, while
  §5.2 evaluates them as the grammar fitted to existing compounds; `table1_novel_lt_half` holds on
  either reading.
* The model gives a bound-N2 compound a probability below 1, so the exceptionless nasalisation of
  (5) is not derived; the modelled experiment has no bound N2s.

## References

* [breiss-katsuda-kawahara-2026b]
* [breiss-katsuda-kawahara-2026a]
* [breiss-2024]
* [breiss-katsuda-kawahara-2021]
* [ito-mester-1997]
* [ito-mester-2003]
* [coetzee-kawahara-2013]
-/

@[expose] public section

namespace BreissKatsudaKawahara2026

open OptimalityTheory HarmonicGrammar Real MeasureTheory

/-- The compound-medial velar, oral [g] or nasal [ŋ]. -/
inductive Velar | oral | nasal
  deriving DecidableEq, Fintype

instance : MeasurableSpace Velar := ⊤
instance : MeasurableSingletonClass Velar := ⟨fun _ ↦ trivial⟩

/-- A listed allomorph, given by its medial velar and its resting activation. -/
structure Base where
  velar : Velar
  activation : ℝ

/-- A compound's listed bases (§4.1), the free-standing N2 if the N2 is free and the whole
compound if it is an existing word. -/
structure Item where
  n2 : Option Base
  compound : Option Base

/-- A free N2 is listed with the [g] it shows word-initially. -/
def freeN2 (a : ℝ) : Base := ⟨.oral, a⟩

/-- An existing compound is listed with its medial velar nasalised. -/
def storedCompound (b : ℝ) : Base := ⟨.nasal, b⟩

/-- A novel compound with a free N2. -/
def novel (a : ℝ) : Item := ⟨some (freeN2 a), none⟩

/-- An existing compound with a free N2. -/
def existing (a b : ℝ) : Item := ⟨some (freeN2 a), some (storedCompound b)⟩

/-- An existing compound with a bound N2. -/
def bound (b : ℝ) : Item := ⟨none, some (storedCompound b)⟩

/-! ### Constraints, scaled violations, and the MaxEnt probability -/

/-- Identity in [nasal] to an optional listed base (6b, c) is violated when the candidate's velar
differs from the base's, and never without a base. -/
def idNasal : Option Base → Constraint Velar
  | some β => Constraint.binary (· ≠ β.velar)
  | none => 0

/-- The constraint set (6), `*INTERNAL-[g]` and identity in [nasal] to the N2 and to the
compound. -/
def con (it : Item) : ConstraintSet Velar (Fin 3) :=
  ![Constraint.binary (· = .oral), idNasal it.n2, idNasal it.compound]

/-- The resting activation of an optional base, zero without one. -/
def activation : Option Base → ℝ
  | some β => β.activation
  | none => 0

/-- The activations by which an item scales the violations of (6) (§4.2), each faithfulness
constraint's by the activation of its base and markedness's not at all. -/
def activations (it : Item) : Fin 3 → ℝ :=
  ![1, activation it.n2, activation it.compound]

/-- The violation vector of a candidate realisation of an item, its violations of (6) scaled by
the item's activations, as the tableaux display them. -/
def violations (it : Item) (v : Velar) : Fin 3 → ℝ :=
  activations it * (con it).violations v

/-- The weights of the three constraints. -/
structure Weights where
  markedness : ℝ
  n2 : ℝ
  compound : ℝ

/-- The weights as a vector indexed like `con`. -/
def Weights.vec (w : Weights) : Fin 3 → ℝ :=
  ![w.markedness, w.n2, w.compound]

/-- The Voting Bases grammar's MaxEnt distribution of an item's realisations. -/
noncomputable def votingBases (w : Weights) (it : Item) : Measure Velar :=
  maxEnt (violations it) w.vec

/-- The probability that the compound nasalises. -/
noncomputable def pNasal (w : Weights) (it : Item) : ℝ :=
  (votingBases w it).real {.nasal}

theorem harmony_apply (w : Weights) (it : Item) (v : Velar) :
    harmony (violations it) w.vec v =
      -(w.markedness * (Constraint.binary (· = Velar.oral) v : ℝ) +
        w.n2 * (activation it.n2 * idNasal it.n2 v) +
        w.compound * (activation it.compound * idNasal it.compound v)) := by
  simp [harmony, dotProduct, Fin.sum_univ_three, violations, activations, con, Weights.vec]

/-- Scaling the violations by the activations is scaling the weights by them (§4.2, §6.3). -/
theorem harmony_violations_eq (w : Weights) (it : Item) :
    harmony (violations it) w.vec = harmonyScore (con it) (w.vec * activations it) := by
  funext v
  simp only [harmony, harmonyScore, violations, dotProduct, Pi.mul_apply,
    ConstraintSet.violations_apply, mul_assoc]

/-- A base's pull toward nasalisation is its activation, signed by its listed velar. -/
def pull : Option Base → ℝ
  | some ⟨.oral, a⟩ => -a
  | some ⟨.nasal, a⟩ => a
  | none => 0

@[simp] theorem pull_freeN2 (a : ℝ) : pull (some (freeN2 a)) = -a := rfl
@[simp] theorem pull_storedCompound (b : ℝ) : pull (some (storedCompound b)) = b := rfl
@[simp] theorem pull_none : pull none = 0 := rfl

theorem pNasal_eq_sigmoid (w : Weights) (it : Item) :
    pNasal w it = sigmoid (w.markedness + w.n2 * pull it.n2 + w.compound * pull it.compound) := by
  rw [pNasal, votingBases, maxEnt_real_singleton_of_pair _ _ (a := Velar.nasal) (b := .oral)
    (by decide) (by decide)]
  congr 1
  obtain ⟨n2, c⟩ := it
  rcases n2 with _ | ⟨_ | _, a⟩ <;> rcases c with _ | ⟨_ | _, b⟩ <;>
    simp [harmony_apply, idNasal, activation, pull] <;> ring

/-! ### The frequency effects -/

theorem pNasal_existing (w : Weights) (a b : ℝ) :
    pNasal w (existing a b) = sigmoid (w.markedness - w.n2 * a + w.compound * b) := by
  simp [pNasal_eq_sigmoid, existing, sub_eq_add_neg]

theorem pNasal_novel (w : Weights) (a : ℝ) :
    pNasal w (novel a) = sigmoid (w.markedness - w.n2 * a) := by
  simp [pNasal_eq_sigmoid, novel, sub_eq_add_neg]

/-- A bound N2 (5) has no free base. -/
theorem pNasal_bound (w : Weights) (b : ℝ) :
    pNasal w (bound b) = sigmoid (w.markedness + w.compound * b) := by
  simp [pNasal_eq_sigmoid, bound]

/-- The more active the free N2, the less an existing compound nasalises (Figure 2, right). -/
theorem existing_strictAnti_n2 (w : Weights) (hw : 0 < w.n2) (b : ℝ) :
    StrictAnti fun a ↦ pNasal w (existing a b) := fun _ _ h ↦ by
  simp only [pNasal_existing]
  exact sigmoid_lt (by nlinarith)

/-- The more active the stored compound, the more it nasalises (Figure 2, left). -/
theorem existing_strictMono_compound (w : Weights) (hw : 0 < w.compound) (a : ℝ) :
    StrictMono fun b ↦ pNasal w (existing a b) := fun _ _ h ↦ by
  simp only [pNasal_existing]
  exact sigmoid_lt (by nlinarith)

/-- The N2 effect persists, with the same sign, in novel compounds (Figure 3). -/
theorem novel_strictAnti_n2 (w : Weights) (hw : 0 < w.n2) :
    StrictAnti fun a ↦ pNasal w (novel a) := fun _ _ h ↦ by
  simp only [pNasal_novel]
  exact sigmoid_lt (by nlinarith)

/-- The N2 effect on the log-odds of nasalisation is the same in an existing compound as in a
novel one, the stored compound adding a constant, so the frequency effect is uniform across
existing and novel compounds (§3.2). -/
theorem logit_pNasal_existing (w : Weights) (a b : ℝ) :
    logit (pNasal w (existing a b)) = logit (pNasal w (novel a)) + w.compound * b := by
  rw [pNasal_existing, pNasal_novel, logit_sigmoid, logit_sigmoid]

theorem novel_lt_existing (w : Weights) (hw : 0 < w.compound) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    pNasal w (novel a) < pNasal w (existing a b) := by
  rw [pNasal_novel, pNasal_existing]
  exact sigmoid_lt (by nlinarith)

/-- Only a free N2 is listed with [g], so a free N2 lowers nasalisation below that of a bound N2
under the same compound, (2)–(4) against (5). -/
theorem existing_lt_bound (w : Weights) (hw : 0 < w.n2) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    pNasal w (existing a b) < pNasal w (bound b) := by
  rw [pNasal_existing, pNasal_bound]
  exact sigmoid_lt (by nlinarith)

theorem bound_half_le (w : Weights) (hM : 0 ≤ w.markedness) (hC : 0 ≤ w.compound) {b : ℝ}
    (hb : 0 ≤ b) : 2⁻¹ ≤ pNasal w (bound b) := by
  rw [pNasal_bound, ← sigmoid_zero]
  exact sigmoid_le (add_nonneg hM (mul_nonneg hC hb))

/-- With `*INTERNAL-[g]` at zero weight nasalisation is the majority outcome exactly when the
compound base's weighted activation exceeds the N2 base's (§5.1, §6.2). -/
theorem zero_markedness_iff (w : Weights) (hM : w.markedness = 0) (a b : ℝ) :
    2⁻¹ < pNasal w (existing a b) ↔ w.n2 * a < w.compound * b := by
  rw [pNasal_existing, ← sigmoid_zero, sigmoid_lt_iff, hM]
  constructor <;> intro h <;> linarith

/-! ### The fitted grammar -/

/-- The fitted weights of Table 1. -/
noncomputable def table1 : Weights := ⟨0, 7.39, 7.09⟩

/-- Under the fitted weights a novel compound, with an activation `σ(f)` for its N2's centred
log-frequency `f` (§4.4), nasalises less than half the time; §5.2 reports predicted rates from
0.002 to 0.39 against observed rates up to 0.79. -/
theorem table1_novel_lt_half (f : ℝ) : pNasal table1 (novel (sigmoid f)) < 2⁻¹ := by
  rw [pNasal_novel, ← sigmoid_zero]
  exact sigmoid_lt (by norm_num [table1]; exact sigmoid_pos f)

/-! ### The schematic tableaux -/

/-- The weights of tableaux (7) and (8). -/
def w78 : Weights := ⟨2, 1, 1⟩

/-- The weights of tableau (9). -/
noncomputable def w9 : Weights := ⟨0.1, 1, 2⟩

/-- Tableau (7) evaluates novel compounds whose N2s have activations 0.7 and 0.3, and the more
active N2 pulls harder toward [g]. -/
theorem tableau7 :
    harmony (violations (novel 0.7)) w78.vec .oral = -2 ∧
      harmony (violations (novel 0.7)) w78.vec .nasal = -0.7 ∧
      harmony (violations (novel 0.3)) w78.vec .oral = -2 ∧
      harmony (violations (novel 0.3)) w78.vec .nasal = -0.3 ∧
      pNasal w78 (novel 0.7) = sigmoid 1.3 ∧ pNasal w78 (novel 0.3) = sigmoid 1.7 ∧
      pNasal w78 (novel 0.7) < pNasal w78 (novel 0.3) := by
  simp only [pNasal_novel]
  norm_num [harmony_apply, sigmoid_lt_iff, idNasal, activation, novel, freeN2, w78]

/-- Tableau (8) evaluates existing compounds with N2 activation 0.5 and compound activations 0.7
and 0.3. The more active compound nasalises more, and either nasalises more than the same N2
without a stored compound. -/
theorem tableau8 :
    harmony (violations (existing 0.5 0.7)) w78.vec .oral = -2.7 ∧
      harmony (violations (existing 0.5 0.7)) w78.vec .nasal = -0.5 ∧
      harmony (violations (existing 0.5 0.3)) w78.vec .oral = -2.3 ∧
      harmony (violations (existing 0.5 0.3)) w78.vec .nasal = -0.5 ∧
      pNasal w78 (existing 0.5 0.7) = sigmoid 2.2 ∧ pNasal w78 (existing 0.5 0.3) = sigmoid 1.8 ∧
      pNasal w78 (existing 0.5 0.3) < pNasal w78 (existing 0.5 0.7) ∧
      pNasal w78 (novel 0.5) < pNasal w78 (existing 0.5 0.3) := by
  simp only [pNasal_existing, pNasal_novel]
  norm_num [harmony_apply, sigmoid_lt_iff, idNasal, activation, existing, freeN2, storedCompound,
    w78]

/-- The probability of (8b) is below 0.905, so it rounds to 0.90, not to the printed 0.91. -/
theorem pNasal_tableau8b_lt : pNasal w78 (existing 0.5 0.7) < 0.905 := by
  have he : exp 2.2 < 9.3 := by
    have h1 := exp_one_lt_d9
    have h2 := exp_bound_div_one_sub_of_interval' (x := 0.2) (by norm_num) (by norm_num)
    have h3 : exp 2.2 = exp 1 * exp 1 * exp 0.2 := by rw [← exp_add, ← exp_add]; norm_num
    rw [h3]
    nlinarith [exp_pos 1, exp_pos 0.2]
  have hi := (inv_lt_inv₀ (by norm_num) (exp_pos 2.2)).2 he
  rw [pNasal_existing, sigmoid_def, inv_lt_comm₀ (by positivity) (by norm_num)]
  norm_num [w78, exp_neg] at hi ⊢
  linarith

/-- Tableau (9) weakens markedness and strengthens faithfulness to the compound. The nasal
candidate is still the majority outcome for either compound of (8), and the compound effect keeps
its sign. -/
theorem tableau9 :
    harmony (violations (existing 0.5 0.7)) w9.vec .oral = -1.5 ∧
      harmony (violations (existing 0.5 0.7)) w9.vec .nasal = -0.5 ∧
      harmony (violations (existing 0.5 0.3)) w9.vec .oral = -0.7 ∧
      harmony (violations (existing 0.5 0.3)) w9.vec .nasal = -0.5 ∧
      pNasal w9 (existing 0.5 0.7) = sigmoid 1 ∧ pNasal w9 (existing 0.5 0.3) = sigmoid 0.2 ∧
      2⁻¹ < pNasal w9 (existing 0.5 0.3) ∧
      pNasal w9 (existing 0.5 0.3) < pNasal w9 (existing 0.5 0.7) := by
  simp only [pNasal_existing, ← sigmoid_zero]
  norm_num [harmony_apply, sigmoid_lt_iff, idNasal, activation, existing, freeN2, storedCompound,
    w9, -sigmoid_zero]

end BreissKatsudaKawahara2026
