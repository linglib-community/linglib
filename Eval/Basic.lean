module

public import Mathlib.Basic.Sign.Defs
public import Mathlib.Data.Set.Basic
public import Linglib.Data.Statistics.Schema

/-!
# Evaluating accounts against data

This library evaluates the accounts that linglib formalizes against the data it records. An
account's verdict on an observation is right, wrong, or silent when the account predicts nothing
about it or nothing was observed (`Eval.Verdict`). A verdict is always derived from the account's
own definitions and the recorded data, and the comparison it makes is fixed by the type of the
prediction, never by a label attached to an account or a datum.

An experiment is scored cell by cell (`Eval.Experiment`): it records the outcome observed in each
cell of its design, and its linking hypothesis says what outcome a theory predicts there. The
verdict on a theory in a cell compares the two (`Experiment.verdict`). Whatever a theory brings to
the comparison, such as how it parses the experiment's sentences, is part of what is scored, so
that the cells are the facts alone.

A verdict can also name both auxiliaries it rests on (`Eval.Contrasts`). Each cell is a contrast the
experiment tested, and its parameter is, for instance, the sign of the population difference. A
linking hypothesis maps what a theory says about the contrast's stimuli to the region of the
parameter it allows, and a decision rule maps the recorded test to the region the data establish,
as a test significant at a level establishes the sign of the estimated difference
(`significance`). The theory is wrong when the two regions are disjoint, and right when the
established region lies inside the allowed one and the test could have refuted it
(`Verdict.ofRegions`). A significance test can therefore refute a null prediction but never
confirm one, and weakening a prediction never makes it wrong
(`Verdict.ofRegions_eq_wrong_of_subset`). An experiment separates two theories in a contrast under
a class of linking hypotheses when their predictions are disjoint under each (`Contrasts.Crucial`).

The library is linglib's part of the Co-Linguistics project of Chemla, Spector, Kalomoiros and
Schlenker, which compares formalized theories against data.

## References

* [chemla-spector-kalomoiros-schlenker-2026]
-/

@[expose] public section

namespace Eval

/-- An account's verdict on an observation. -/
inductive Verdict where
  /-- The prediction matches the observation. -/
  | correct
  /-- The prediction differs from the observation. -/
  | wrong
  /-- The account predicts nothing, or nothing was observed. -/
  | silent
  deriving DecidableEq, Repr

/-- The verdict of a prediction on an observation of the same type. -/
def Verdict.of {α : Type*} [DecidableEq α] : Option α → Option α → Verdict
  | some p, some o => if p = o then .correct else .wrong
  | _, _ => .silent

/-- An experiment scoring theories `Θ`, with cells `C` and outcomes `O`: the outcome observed in
each cell, and the outcome its linking hypothesis has a theory predict there. -/
structure Experiment (Θ C O : Type*) where
  /-- The outcome observed in a cell, if the cell was run. -/
  observed : C → Option O
  /-- The outcome a theory predicts in a cell by the linking hypothesis, if it predicts one. -/
  predicted : Θ → C → Option O

/-- The verdict on a theory in a cell of an experiment. -/
def Experiment.verdict {Θ C O : Type*} [DecidableEq O] (X : Experiment Θ C O) (T : Θ) (c : C) :
    Verdict :=
  .of (X.predicted T c) (X.observed c)

/-! ### Verdicts by regions -/

section Regions

variable {Ω : Type*}

open Classical in
/-- The verdict on a prediction `P` against a finding `E`, where `𝓔` holds the findings the test
could have produced: wrong when the finding excludes the prediction, correct when the finding lies
inside a prediction that some possible finding would have refuted, and silent otherwise. -/
noncomputable def Verdict.ofRegions (𝓔 : Set (Set Ω)) (P E : Set Ω) : Verdict :=
  if Disjoint E P then .wrong
  else if E ⊆ P ∧ ∃ E' ∈ 𝓔, Disjoint E' P then .correct else .silent

namespace Verdict

variable {𝓔 : Set (Set Ω)} {P P' E : Set Ω}

theorem ofRegions_eq_wrong_iff : ofRegions 𝓔 P E = .wrong ↔ Disjoint E P := by
  unfold ofRegions
  split_ifs <;> simp_all

theorem ofRegions_eq_correct (hE : E.Nonempty) (h : E ⊆ P) (hP : ∃ E' ∈ 𝓔, Disjoint E' P) :
    ofRegions 𝓔 P E = .correct := by
  have hd : ¬ Disjoint E P :=
    Set.not_disjoint_iff_nonempty_inter.2 (by rwa [Set.inter_eq_left.2 h])
  rw [ofRegions, ite_eq_right hd, ite_eq_left ⟨h, hP⟩]

/-- A finding that establishes nothing gives a silent verdict on a prediction that allows
something without allowing everything. -/
theorem ofRegions_univ_right (hP : P.Nonempty) (hP' : P ≠ .univ) :
    ofRegions 𝓔 P .univ = .silent := by
  rw [ofRegions, ite_eq_right (by simpa [Set.univ_disjoint] using hP.ne_empty),
    ite_eq_right fun h ↦ hP' (Set.univ_subset_iff.1 h.1)]

/-- A prediction that allows everything is never credited. -/
theorem ofRegions_univ_left (h𝓔 : ∀ E' ∈ 𝓔, E'.Nonempty) (hE : E.Nonempty) :
    ofRegions 𝓔 .univ E = .silent := by
  rw [ofRegions, ite_eq_right (by simpa [Set.disjoint_univ] using hE.ne_empty),
    ite_eq_right fun ⟨_, E', hE', h⟩ ↦ (h𝓔 E' hE').ne_empty (Set.disjoint_univ.1 h)]

/-- Weakening a prediction never makes the verdict on it wrong. -/
theorem ofRegions_eq_wrong_of_subset (h : P ⊆ P') (hw : ofRegions 𝓔 P' E = .wrong) :
    ofRegions 𝓔 P E = .wrong :=
  ofRegions_eq_wrong_iff.2 ((ofRegions_eq_wrong_iff.1 hw).mono_right h)

end Verdict

open Data.Statistics in
/-- The decision rule of significance at level `α`, from the estimated difference and the p-value
of the test of a contrast, if one is reported: a test significant at `α` establishes the sign of the
difference, and any other test, or none, establishes nothing. -/
def significance (α : ℚ) : ℚ × Option PValue → Set SignType
  | (d, some p) => if p.Significant α then {SignType.sign d} else .univ
  | (_, none) => .univ

open Data.Statistics in
theorem significance_of_significant {α d : ℚ} {p : PValue} (h : p.Significant α) :
    significance α (d, some p) = {SignType.sign d} :=
  ite_eq_left h

open Data.Statistics in
theorem significance_of_not_significant {α d : ℚ} {p : PValue} (h : ¬ p.Significant α) :
    significance α (d, some p) = .univ :=
  ite_eq_right h

/-- The tested contrasts `C` of an experiment: the record `S` of each contrast's tests, and what
each theory `Θ` says about a contrast's stimuli, `R`. -/
structure Contrasts (Θ C R S : Type*) where
  /-- What the experiment records about a contrast. -/
  record : C → S
  /-- What a theory says about the stimuli of a contrast. -/
  reading : Θ → C → R

namespace Contrasts

variable {Θ C R S : Type*}

/-- The verdict on a theory in a contrast, under a decision rule `δ` and a linking hypothesis `ℓ`:
the region the record establishes against the region the theory's reading allows, among the
regions a record could establish. -/
noncomputable def verdict (X : Contrasts Θ C R S) (δ : S → Set Ω) (ℓ : R → Set Ω) (T : Θ)
    (c : C) : Verdict :=
  .ofRegions (Set.range δ) (ℓ (X.reading T c)) (δ (X.record c))

/-- An experiment separates two theories in a contrast under every linking hypothesis of a class
`𝓛` when their predictions there are disjoint. -/
def Crucial (X : Contrasts Θ C R S) (𝓛 : Set (R → Set Ω)) (T₁ T₂ : Θ) (c : C) : Prop :=
  ∀ ℓ ∈ 𝓛, Disjoint (ℓ (X.reading T₁ c)) (ℓ (X.reading T₂ c))

/-- Theories that read a contrast alike get the same verdict there. -/
theorem verdict_congr (X : Contrasts Θ C R S) (δ : S → Set Ω) (ℓ : R → Set Ω) {T T' : Θ} {c : C}
    (h : X.reading T c = X.reading T' c) : X.verdict δ ℓ T c = X.verdict δ ℓ T' c := by
  rw [verdict, verdict, h]

end Contrasts

end Regions

end Eval
