module

public import Eval.Basic

/-!
# Inference endorsement

In an inference-endorsement task, subjects rate how far a response option follows from a sentence.
What a theory says about a cell of such a task is which options it predicts from the sentence,
together with the entailments between the options, which belong to the stimuli
(`Eval.Endorsement`). A linking hypothesis turns that reading into a prediction about the contrast
between two options `a` and `b`: the sign of the difference between their ratings.

Three linking hypotheses are registered. The strongest predicted option gets the advantage, as in
Chemla and Schlenker's summary of their predictions (`strongest`). Subjects endorse exactly the
predicted options (`exactly`). Subjects prefer the weaker of two predicted options, the explanation
Chemla and Schlenker set aside (`weaker`). All three favor the predicted option: from a theory that
predicts one option and not the other, they predict its advantage (`FavorsPredicted`). So a theory
that predicts `a` alone and a theory that predicts `b` alone are separated by every linking
hypothesis that favors the predicted option (`disjoint_of_favorsPredicted`); the three differ only
when a theory predicts both options or neither.

## References

* [chemla-schlenker-2012]
-/

@[expose] public section

namespace Eval

/-- What a theory says about a cell of an inference-endorsement task with response options `ι`:
the options it predicts from the sentence, and the entailments between the options, which belong
to the stimuli. -/
structure Endorsement (ι : Type*) where
  /-- The options the theory predicts. -/
  predicted : Set ι
  /-- Whether one option entails another. -/
  entails : ι → ι → Prop

namespace Endorsement

variable {ι : Type*} (a b : ι)

open Classical in
/-- The strongest predicted option gets the advantage. In the contrast of `a` against `b`, `a` is
rated higher when it is predicted and `b` is either not predicted or entailed by `a`, and lower in
the converse case. -/
noncomputable def strongest (r : Endorsement ι) : Set SignType :=
  if a ∈ r.predicted ∧ (b ∈ r.predicted → r.entails a b) then {.pos}
  else if b ∈ r.predicted ∧ (a ∈ r.predicted → r.entails b a) then {.neg} else .univ

open Classical in
/-- Subjects endorse exactly the predicted options: a predicted option is rated higher than an
unpredicted one, and two predicted options are rated alike. -/
noncomputable def exactly (r : Endorsement ι) : Set SignType :=
  if a ∈ r.predicted ∧ b ∉ r.predicted then {.pos}
  else if b ∈ r.predicted ∧ a ∉ r.predicted then {.neg}
  else if a ∈ r.predicted then {.zero} else .univ

open Classical in
/-- Subjects prefer the weaker of two predicted options. In the contrast of `a` against `b`, `a` is
rated higher when it is predicted and `b` is either not predicted or entails `a`, and lower in the
converse case. -/
noncomputable def weaker (r : Endorsement ι) : Set SignType :=
  if a ∈ r.predicted ∧ (b ∈ r.predicted → r.entails b a) then {.pos}
  else if b ∈ r.predicted ∧ (a ∈ r.predicted → r.entails a b) then {.neg} else .univ

/-- A linking hypothesis favors the predicted option when, from a theory that predicts exactly one
of `a` and `b`, it predicts the advantage of that one. -/
def FavorsPredicted (ℓ : Endorsement ι → Set SignType) : Prop :=
  ∀ r : Endorsement ι, (a ∈ r.predicted → b ∉ r.predicted → ℓ r = {.pos}) ∧
    (b ∈ r.predicted → a ∉ r.predicted → ℓ r = {.neg})

theorem favorsPredicted_strongest : FavorsPredicted a b (strongest a b) := fun r ↦
  ⟨fun ha hb ↦ by simp [strongest, ha, hb], fun hb ha ↦ by simp [strongest, ha, hb]⟩

theorem favorsPredicted_exactly : FavorsPredicted a b (exactly a b) := fun r ↦
  ⟨fun ha hb ↦ by simp [exactly, ha, hb], fun hb ha ↦ by simp [exactly, ha, hb]⟩

theorem favorsPredicted_weaker : FavorsPredicted a b (weaker a b) := fun r ↦
  ⟨fun ha hb ↦ by simp [weaker, ha, hb], fun hb ha ↦ by simp [weaker, ha, hb]⟩

variable {a b}

/-- A linking hypothesis that favors the predicted option separates a reading that predicts `a`
alone from one that predicts `b` alone. -/
theorem disjoint_of_favorsPredicted {ℓ : Endorsement ι → Set SignType}
    (hℓ : FavorsPredicted a b ℓ) {r r' : Endorsement ι} (ha : a ∈ r.predicted)
    (hb : b ∉ r.predicted) (hb' : b ∈ r'.predicted) (ha' : a ∉ r'.predicted) :
    Disjoint (ℓ r) (ℓ r') := by
  rw [(hℓ r).1 ha hb, (hℓ r').2 hb' ha', Set.disjoint_singleton]
  decide

end Endorsement

end Eval
