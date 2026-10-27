module

public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Logic.Trivalent.Basic
public import Linglib.Data.Examples.TieuEtAl2020

/-!
# Tieu, Bill, Romoli and Crain (2020): Testing Theories of Plural Meanings

This file formalizes the three theories of the multiplicity inference of the English plural that
Tieu, Bill, Romoli and Crain test experimentally, and the predictions on which they diverge. *Emily
fed giraffes* conveys that she fed more than one, (1), while *Emily didn't feed giraffes* conveys
that she fed none, (2), and the inference likewise disappears in conditional antecedents and
questions, (3)–(4). The ambiguity approach of Farkas and de Swart gives the plural a weak reading,
one or more, and a strong reading, more than one, and selects the stronger by the Strongest Meaning
Hypothesis, (5)–(7). The implicature approach of Spector and of Zweig gives the plural the weak
meaning and derives the multiplicity inference by exhaustification against the singular alternative,
(13)–(15), which is entailed rather than excludable under negation, (16)–(17). The homogeneity
approach of Križ, extended to bare plurals, makes the plural predicate undefined of a single
giraffe, so the sentence is true of more than one, false of none and undefined otherwise, (20)–(24).
All three predict the monotonicity pattern, `readings_positive` and `readings_negative`. They
diverge in a context where Emily fed exactly one giraffe, (27): the implicature approach makes the
positive sentence literally true with a false implicature and the negative one false, while the
ambiguity approach makes both false and the homogeneity approach both undefined, `singular_context`.
The implicature approach alone derives the multiplicity inference by the mechanism of the *not all*
inference of *some*, (29), the same exhaustifier against a stronger alternative, `exhIE_some`,
whence its uniformity prediction, (28), that children compute fewer of both.

## Implementation notes

The worlds are the number of giraffes fed, so the readings are sets of natural numbers and
negation is complementation. The implicature approach is the innocent-exclusion exhaustifier
of `Semantics.Exhaustification.InnocentExclusion` with the singular alternative; the paper's
versions differ in how they derive that alternative, footnote 4, and agree on the result. The
Strongest Meaning Hypothesis picks the least reading under entailment, `IsLeast`. Homogeneity
is a trivalent predicate whose negation is `Neg.neg`. The experiments are not formalized:
in Experiment 1, a truth-value judgment task, adults rejected positive plural sentences after a
story with one animal fed far more often than four- and five-year-olds did, and accepted the
negative ones only moderately; in Experiment 2 children computed fewer multiplicity inferences
and fewer *not all* implicatures than adults, and the two rates were correlated within
children; in Experiment 3, a ternary judgment task, adults gave the positive plural in a
singular context an intermediate reward and the negative plural the minimal one. The examples
are the rows of `Data.Examples.TieuEtAl2020`.

## References

* [tieu-etal-2020]
* [farkas-de-swart-2010]
* [spector-2007b]
* [zweig-2009]
* [kriz-2015]
* [fox-2007]
-/

@[expose] public section

namespace TieuEtAl2020

open Exhaustification

/-! ### Plural meanings over the number of giraffes fed -/

/-- The weak reading is one or more (5a). -/
def weak : Set ℕ := {n | 1 ≤ n}

/-- The strong reading is more than one, the multiplicity inference (5b). -/
def strong : Set ℕ := {n | 2 ≤ n}

/-- The singular alternative is exactly one (14). -/
def singular : Set ℕ := {1}

/-! ### The implicature approach (section 1.2.2) -/

-- (13), (15)
theorem exhIE_weak : exhIE {weak, singular} weak = strong := by
  rw [exhIE_pair_sdiff (φ := weak) (d := singular) ⟨2, by simp [weak, singular]⟩]
  ext n
  simp only [weak, singular, strong, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  omega

-- (16), (17)
theorem exhIE_compl_weak : exhIE {weakᶜ, singularᶜ} weakᶜ = weakᶜ := by
  ext n
  rw [mem_exhIE_iff]
  refine ⟨And.left, fun h ↦ ⟨h, fun a ha ↦ ?_⟩⟩
  have hsub : weakᶜ ⊆ a := by
    rcases Set.mem_insert_iff.1 ha.1 with rfl | h
    · exact subset_rfl
    · rw [Set.mem_singleton_iff] at h
      subst h
      intro m hm
      simp only [weak, singular, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le,
        Set.mem_singleton_iff] at hm ⊢
      omega
  exact absurd ha (not_isInnocentlyExcludable_of_phi_subset (Set.toFinite _)
    ⟨0, by show (0 : ℕ) ∈ weakᶜ; simp [weak]⟩ hsub)

/-- The *not all* implicature of *some of the k giraffes* is exhaustification against *all* (29), as
the uniformity prediction (28) requires. -/
theorem exhIE_some {k : ℕ} (hk : 2 ≤ k) :
    exhIE {{n | 1 ≤ n}, {k}} {n | 1 ≤ n} = {n | 1 ≤ n ∧ n ≠ k} := by
  rw [exhIE_pair_sdiff (φ := {n | 1 ≤ n}) (d := {k}) ⟨1, by simp; omega⟩]
  ext n
  simp

/-! ### The ambiguity approach (section 1.2.1)

The Strongest Meaning Hypothesis (7) prefers, among the readings of a plural sentence, the one
entailing all the others: the least reading under inclusion, `IsLeast`. -/

-- (5)
theorem isLeast_strong : IsLeast {weak, strong} strong :=
  ⟨by simp, by
    rintro r (rfl | rfl)
    · intro n hn
      simp only [weak, strong, Set.mem_ofPred_eq] at hn ⊢
      omega
    · exact le_rfl⟩

-- (6)
theorem isLeast_compl_weak : IsLeast {weakᶜ, strongᶜ} weakᶜ :=
  ⟨by simp, by
    rintro r (rfl | rfl)
    · exact le_rfl
    · intro n hn
      simp only [weak, strong, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hn ⊢
      omega⟩

/-! ### The homogeneity approach (section 1.2.3) -/

/-- The plural sentence is true of a plurality of giraffes, false of none and undefined
otherwise, (20)–(22). -/
def homogeneous (n : ℕ) : SignType :=
  if 2 ≤ n then 1 else if n = 0 then -1 else 0

theorem homogeneous_eq_one_iff {n : ℕ} : homogeneous n = 1 ↔ 2 ≤ n := by
  rcases n with _ | _ | n <;> simp [homogeneous]

-- (23), (24)
theorem neg_homogeneous_eq_one_iff {n : ℕ} : -homogeneous n = 1 ↔ n = 0 := by
  rcases n with _ | _ | n <;> simp [homogeneous]

/-! ### Predictions (section 1.3) -/

theorem readings_positive :
    exhIE {weak, singular} weak = strong ∧ IsLeast {weak, strong} strong ∧
      {n | homogeneous n = 1} = strong :=
  ⟨exhIE_weak, isLeast_strong, Set.ext fun _ ↦ homogeneous_eq_one_iff⟩

theorem readings_negative :
    exhIE {weakᶜ, singularᶜ} weakᶜ = weakᶜ ∧ IsLeast {weakᶜ, strongᶜ} weakᶜ ∧
      {n | -homogeneous n = 1} = weakᶜ := by
  refine ⟨exhIE_compl_weak, isLeast_compl_weak, Set.ext fun n ↦ ?_⟩
  rw [Set.mem_ofPred_eq, neg_homogeneous_eq_one_iff]
  simp [weak]

/-- In the singular context (27) the implicature approach treats the positive and negative sentences
asymmetrically, while the ambiguity and homogeneity approaches do not. -/
theorem singular_context :
    (1 ∈ weak ∧ 1 ∉ exhIE {weak, singular} weak ∧
        1 ∉ exhIE {weakᶜ, singularᶜ} weakᶜ) ∧
      (1 ∉ strong ∧ 1 ∉ weakᶜ) ∧
      (homogeneous 1 = 0 ∧ -homogeneous 1 = 0) := by
  rw [exhIE_weak, exhIE_compl_weak]
  simp [weak, strong, homogeneous]

end TieuEtAl2020
