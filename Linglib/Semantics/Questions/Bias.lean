module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Filter.Basic
public import Linglib.Semantics.Negation.Polarity

/-!
# Polar question bias

A polar question can be biased toward one of its answers. Two bodies of information bear on this:
the evidence available in the context, and what the speaker believed beforehand. A body of
information is a filter of propositions, the ones it supports, and its *bias* on a proposition
`p` is `1` when it supports `p`, `-1` when it supports `¬p` and `0` when it supports neither. A
consistent body never supports both, and its bias on `¬p` is the negative of its bias on `p`, so
the action of the polarities on signs is the one induced by their action on propositions. An
information state is biased on `p` exactly when it is included in `p` or in its complement, that
is, when it resolves the polar question over `p`.

A situation is the pair of the two biases. Following [sudo-2013], a bias value is a set of signs,
the ones that a question form is compatible with: the value [+s] holds of a consistent body when
it supports the `s` proposition, and [−s] when it does not. A `BiasProfile` gives one bias value
for the evidence and one for the prior belief, and its `felicity` is the set of situations in
which the form can be used.

## Main definitions

* `Question.bias`: the bias of a body of information on a proposition.
* `Question.BiasValue.plus`, `Question.BiasValue.minus`, `Question.BiasValue.neutral`: the values
  [+s], [−s] and [neutral].
* `Question.BiasProfile`: an evidential and an epistemic bias value.
* `Question.BiasProfile.felicity`: the situations a profile admits.

## Main results

* `Question.bias_smul`: reading a consistent body of information for `¬p` negates its bias.
* `Question.bias_mem_plus_iff`, `Question.bias_mem_minus_iff`: the values [+s] and [−s] hold of a
  consistent body when it supports, or does not support, the `s` proposition.

## Implementation notes

* A body of information is a `Filter`, as the common ground is in `Discourse/CommonGround.lean`.
  An information state `σ` is the principal filter `𝓟 σ`, and the worlds an agent considers
  possible at `w` are the state `{v | w ~[R] v}`. The inconsistent body `⊥` supports everything;
  the definition gives it the bias `1`, and the lemmas about `-1` assume `F.NeBot`.
* The bias is the sign of the answer a body of information settles. Nothing in it is specific
  to questions: the polar question over `p` enters through `Inquisitive.Proposition.mem_polar`,
  whose right-hand side is that of `bias_principal_ne_zero_iff`.
* An account on which evidence raises the probability of a proposition without entailing it maps
  its own contexts to signs, as `Studies/Zheng2025.lean` does.

## References

* [buring-gunlogson-2000]
* [ladd-1981]
* [romero-han-2004]
* [sudo-2013]
-/

@[expose] public section

namespace Question

/-- A situation: the states of the contextual evidence and of the speaker's prior belief. -/
abbrev Situation := SignType × SignType

/-- A bias value ([sudo-2013]): the states of a body of information, the sign of the prejacent
it supports, that a question is compatible with. -/
abbrev BiasValue := Finset SignType

namespace BiasValue

/-- The value [+s] admits only a body of information supporting the `s` proposition. -/
def plus (s : Polarity) : BiasValue := {(s : SignType)}

/-- The value [−s] admits any body of information not supporting the `s` proposition. -/
def minus (s : Polarity) : BiasValue := (plus s)ᶜ

/-- The value [neutral] admits only a body of information supporting neither. -/
def neutral : BiasValue := {0}

variable {s : Polarity} {x : SignType}

@[simp] theorem mem_plus : x ∈ plus s ↔ x = s := Finset.mem_singleton

@[simp] theorem mem_minus : x ∈ minus s ↔ x ≠ s := by simp [minus]

@[simp] theorem mem_neutral : x ∈ neutral ↔ x = 0 := Finset.mem_singleton

@[simp] theorem compl_minus (s : Polarity) : (minus s)ᶜ = plus s := compl_compl _

end BiasValue

/-- A bias profile, the contextual evidence and the prior beliefs of the speaker a question is
compatible with. -/
structure BiasProfile where
  /-- The contextual evidence the question is compatible with. -/
  evidential : BiasValue
  /-- The prior beliefs of the speaker the question is compatible with. -/
  epistemic : BiasValue
  deriving DecidableEq

/-- The situations a profile admits, as pairs of contextual evidence and prior belief. -/
def BiasProfile.felicity (b : BiasProfile) : Finset Situation :=
  b.evidential ×ˢ b.epistemic

@[simp]
theorem BiasProfile.mem_felicity {b : BiasProfile} {s : Situation} :
    s ∈ b.felicity ↔ s.1 ∈ b.evidential ∧ s.2 ∈ b.epistemic :=
  Finset.mem_product

/-! ### The bias of a body of information -/

section Bias

open Filter

variable {W : Type*} {F : Filter W} {p : Set W}

open Classical in
/-- The bias of the body of information `F` on the proposition `p`: `1` when `F` supports `p`,
`-1` when it supports the negation of `p`, and `0` when it supports neither. -/
noncomputable def bias (F : Filter W) (p : Set W) : SignType :=
  if p ∈ F then 1 else if pᶜ ∈ F then -1 else 0

theorem bias_eq_one_iff : bias F p = 1 ↔ p ∈ F := by
  unfold bias; split_ifs <;> simp_all

theorem bias_eq_zero_iff : bias F p = 0 ↔ p ∉ F ∧ pᶜ ∉ F := by
  unfold bias; split_ifs <;> simp_all

theorem bias_eq_neg_one_iff [F.NeBot] : bias F p = -1 ↔ pᶜ ∈ F := by
  unfold bias; split_ifs with h <;> simp_all
  exact compl_notMem h

theorem bias_compl [F.NeBot] (p : Set W) : bias F pᶜ = -bias F p := by
  by_cases h : p ∈ F
  · rw [bias_eq_one_iff.2 h, bias_eq_neg_one_iff.2 (by rwa [compl_compl])]
  · by_cases h' : pᶜ ∈ F
    · rw [bias_eq_one_iff.2 h', bias_eq_neg_one_iff.2 h', neg_neg]
    · rw [bias_eq_zero_iff.2 ⟨h, h'⟩, bias_eq_zero_iff.2 ⟨h', by rwa [compl_compl]⟩, neg_zero]

/-- Reading a consistent body of information for the proposition of the opposite polarity
negates its bias. -/
theorem bias_smul [F.NeBot] (s : Polarity) (p : Set W) : bias F (s • p) = s • bias F p := by
  cases s
  · simp
  · exact bias_compl p

/-- An information state is biased on `p` exactly when it settles `p` or its negation. -/
theorem bias_principal_ne_zero_iff {σ : Set W} : bias (𝓟 σ) p ≠ 0 ↔ σ ⊆ p ∨ σ ⊆ pᶜ := by
  simp only [ne_eq, bias_eq_zero_iff, mem_principal]
  tauto

/-- The value [+s] holds of a consistent body of information that supports the `s`
proposition. -/
theorem bias_mem_plus_iff [F.NeBot] (s : Polarity) : bias F p ∈ BiasValue.plus s ↔ s • p ∈ F := by
  cases s
  · simp [bias_eq_one_iff]
  · simpa using bias_eq_neg_one_iff

/-- The value [−s] holds of a consistent body of information that does not support the `s`
proposition. -/
theorem bias_mem_minus_iff [F.NeBot] (s : Polarity) :
    bias F p ∈ BiasValue.minus s ↔ s • p ∉ F := by
  rw [BiasValue.mem_minus, Ne, ← BiasValue.mem_plus, bias_mem_plus_iff]

end Bias

end Question
