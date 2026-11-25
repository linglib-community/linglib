module

public import Mathlib.Order.Filter.Basic
public import Linglib.Semantics.Negation.Polarity

/-!
# The bias of a body of information

A context holds bodies of information: the evidence available in it, what a participant
believes, the common ground. A body of information is a filter of propositions, the ones it
supports, and its *bias* on a proposition `p` is `1` when it supports `p`, `-1` when it supports
`¬p` and `0` when it supports neither. A consistent body never supports both, and its bias on
`¬p` is the negative of its bias on `p`, so the action of the polarities on signs is the one
induced by their action on propositions. An information state is biased on `p` exactly when it
is included in `p` or in its complement.

## Main definitions

* `Filter.bias`: the bias of a body of information on a proposition.

## Main results

* `Filter.bias_smul`: reading a consistent body of information for `¬p` negates its bias.
* `Filter.bias_principal_ne_zero_iff`: an information state is biased on `p` exactly when it
  settles `p` or its negation.

## Implementation notes

* A body of information is a `Filter`, as the common ground is in `Discourse/CommonGround.lean`.
  An information state `σ` is the principal filter `𝓟 σ`, and the worlds an agent considers
  possible at `w` are the state `{v | w ~[R] v}`. The inconsistent body `⊥` supports everything;
  the definition gives it the bias `1`, and the lemmas about `-1` assume `F.NeBot`.
* The bias is a fact about the context and a proposition. A polar question over `p` enters
  through `Inquisitive.Proposition.mem_polar`, whose right-hand side is that of
  `bias_principal_ne_zero_iff`: a state is biased exactly when it resolves the question.
* An account on which evidence raises the probability of a proposition without entailing it maps
  its own contexts to signs, as `Studies/Zheng2025.lean` does.

## References

* [buring-gunlogson-2000]
* [sudo-2013]
* [romero-han-2004]
-/

@[expose] public section

namespace Filter

variable {W : Type*} {F : Filter W} {p : Set W}

open Classical in
/-- The bias of the body of information `F` on the proposition `p`: `1` when `F` supports `p`,
`-1` when it supports the negation of `p`, and `0` when it supports neither. -/
noncomputable def bias (F : Filter W) (p : Set W) : SignType :=
  if p ∈ F then 1 else if pᶜ ∈ F then -1 else 0

theorem bias_eq_one_iff : F.bias p = 1 ↔ p ∈ F := by
  unfold bias; split_ifs <;> simp_all

theorem bias_eq_zero_iff : F.bias p = 0 ↔ p ∉ F ∧ pᶜ ∉ F := by
  unfold bias; split_ifs <;> simp_all

theorem bias_eq_neg_one_iff [F.NeBot] : F.bias p = -1 ↔ pᶜ ∈ F := by
  unfold bias; split_ifs with h <;> simp_all
  exact compl_notMem h

theorem bias_compl [F.NeBot] (p : Set W) : F.bias pᶜ = -F.bias p := by
  by_cases h : p ∈ F
  · rw [bias_eq_one_iff.2 h, bias_eq_neg_one_iff.2 (by rwa [compl_compl])]
  · by_cases h' : pᶜ ∈ F
    · rw [bias_eq_one_iff.2 h', bias_eq_neg_one_iff.2 h', neg_neg]
    · rw [bias_eq_zero_iff.2 ⟨h, h'⟩, bias_eq_zero_iff.2 ⟨h', by rwa [compl_compl]⟩, neg_zero]

/-- Reading a consistent body of information for the proposition of the opposite polarity
negates its bias. -/
theorem bias_smul [F.NeBot] (s : Polarity) (p : Set W) : F.bias (s • p) = s • F.bias p := by
  cases s
  · simp
  · exact bias_compl p

/-- An information state is biased on `p` exactly when it settles `p` or its negation. -/
theorem bias_principal_ne_zero_iff {σ : Set W} : (𝓟 σ).bias p ≠ 0 ↔ σ ⊆ p ∨ σ ⊆ pᶜ := by
  simp only [ne_eq, bias_eq_zero_iff, mem_principal]
  tauto

end Filter
