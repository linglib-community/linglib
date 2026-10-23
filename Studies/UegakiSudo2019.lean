module

public import Linglib.Semantics.Attitudes.Preference.Degree
public import Linglib.Data.Examples.UegakiSudo2019
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# Uegaki and Sudo (2019): The hope-wh Puzzle

Uegaki and Sudo explain why non-veridical preferential predicates such as *hope*, *wish*,
*expect* and *fear* reject interrogative complements, while veridical ones such as *be happy*
and *like* accept them. A preferential predicate compares the degree to which its subject prefers
an answer with a threshold set by a comparison class of focus alternatives, and it presupposes
Threshold Significance, that some member of the class clears the threshold. With a question, the
comparison class lies inside the question, so *hope* asserts no more than it presupposes and is
true whenever defined; a meaning that is trivial in this way is ungrammatical. With a
declarative, and for veridical predicates, which require the preferred answer to be true and
believed, the meaning stays contingent.

## Main statements

* `hope_question_iff_significance`: with a question, *hope* asserts its presupposition.
* `exists_significance_not_hope_declarative`: with a declarative, *hope* is not trivial.
* `veridical_isDistributive`, `veridicality_breaks_triviality`: veridical predicates are
  clausally distributive and not trivial.

## Implementation notes

The non-veridical predicates are the substrate's degree-comparison predicates,
`Preferential.degreeComparison`, and Threshold Significance is `Degree.ThresholdSignificant`. A
veridical predicate is the same degree comparison applied to the answers that are true and
believed, (26), with belief a predicate parameter. The concrete models measure preference in
the reals. Anand and Hacquard's doxastic condition, (39), the selective focus sensitivity
and exhaustivity refinements of section 4, and the *about*-nominalization of section 5 are not
formalized. The examples are the rows of `Data.Examples.UegakiSudo2019`.

## References

* [uegaki-sudo-2019]
* [villalta-2008]
* [romero-2015]
* [gajewski-2002]
* [anand-hacquard-2013]
-/

@[expose] public section

namespace UegakiSudo2019

open Preferential

variable {W E D : Type*} [LinearOrder D] (μ : E → W → Set W → D) (θ : Set (Set W) → D)

/-! ### Triviality for non-veridical preferentials -/

/-- With the comparison class drawn from the question, (30), Threshold Significance entails the
assertion of *hope* with a question (36). -/
theorem significance_entails_hope_question {C Q : Set (Set W)} (hCQ : C ⊆ Q) (x : E) (w : W)
    (h : Degree.ThresholdSignificant (μ x w) θ C) : degreeComparison μ θ C x Q w :=
  (degreeComparison_iff_thresholdSignificant μ θ C hCQ x w).2 h

/-- With the comparison class inside the question, the assertion of *hope* with a question is its
presupposition, so the meaning is true whenever defined. This is [gajewski-2002]'s L-analyticity,
which makes *hope* anti-rogative. -/
theorem hope_question_iff_significance {C Q : Set (Set W)} (hCQ : C ⊆ Q) (x : E) (w : W) :
    degreeComparison μ θ C x Q w ↔ Degree.ThresholdSignificant (μ x w) θ C :=
  degreeComparison_iff_thresholdSignificant μ θ C hCQ x w

/-- *Hope* with a declarative is not trivial (35). Threshold Significance over the focus
alternatives does not settle whether the subject prefers the one proposition of the complement,
as a model with a preferred alternative and a dispreferred complement shows. -/
theorem exists_significance_not_hope_declarative :
    ∃ (μ : Unit → Bool → Set Bool → ℝ) (θ : Set (Set Bool) → ℝ) (C : Set (Set Bool))
      (A : Set Bool), A ∈ C ∧ Degree.ThresholdSignificant (μ () true) θ C ∧
        ¬ degreeComparison μ θ C () {A} true := by
  classical
  refine ⟨fun _ _ p ↦ if true ∈ p then 1 else -1, fun _ ↦ 0, {{true}, {false}}, {false},
    by simp, ⟨{true}, by simp, by norm_num⟩, ?_⟩
  rw [degreeComparison_singleton, mem_preferred]
  norm_num

/-! ### Veridical preferentials -/

variable (believes : E → Set W → W → Prop)

/-- A veridical preferential such as *be happy* is the degree comparison over the answers that are
true at the world of evaluation and believed by the subject, (24) and (26). -/
def veridical (C : Set (Set W)) (x : E) (Q : Set (Set W)) (w : W) : Prop :=
  degreeComparison μ θ C x (Q ∩ {p | w ∈ p ∧ believes x p w}) w

/-- Veridical preferentials are clausally distributive, so it is veridicality, not a failure of
distributivity, that lets them take questions. -/
theorem veridical_isDistributive (C : Set (Set W)) :
    Distributivity.IsDistributive (veridical μ θ believes C) := fun x Q w ↦ by
  simp only [veridical, degreeComparison, Set.inter_assoc]
  constructor
  · rintro ⟨p, hpQ, hp⟩
    exact ⟨p, hpQ, p, rfl, hp⟩
  · rintro ⟨p, hpQ, q, rfl, hq⟩
    exact ⟨q, hpQ, hq⟩

/-- Veridicality breaks the triviality. In a model where Threshold Significance holds, so that the
non-veridical assertion is true, the veridical assertion is false at a world where the true answer
is not the preferred one. The model has two worlds and the polar question over them, evaluated at
the dispreferred world. -/
theorem veridicality_breaks_triviality :
    ∃ (μ : Unit → Bool → Set Bool → ℝ) (θ : Set (Set Bool) → ℝ)
      (believes : Unit → Set Bool → Bool → Prop) (Q : Set (Set Bool)),
      Degree.ThresholdSignificant (μ () false) θ Q ∧ degreeComparison μ θ Q () Q false ∧
        ¬ veridical μ θ believes Q () Q false := by
  classical
  refine ⟨fun _ _ p ↦ if true ∈ p then 1 else -1, fun _ ↦ 0, fun _ _ _ ↦ True,
    {{true}, {false}}, ⟨{true}, by simp, by norm_num⟩,
    ⟨{true}, by simp, by simp, by norm_num⟩, ?_⟩
  rintro ⟨p, ⟨hp, hw, -⟩, -, hd⟩
  rcases hp with rfl | rfl
  · simp at hw
  · norm_num at hd

end UegakiSudo2019
