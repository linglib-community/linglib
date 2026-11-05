module

public import Linglib.Semantics.Attitudes.Preference.Degree
public import Linglib.Data.Examples.UegakiSudo2019
import Mathlib.Basic.Nontrivial.Basic

/-!
# Uegaki and Sudo (2019): The hope-wh Puzzle

Uegaki and Sudo explain why non-veridical preferential predicates such as *hope*, *wish*,
*expect* and *fear* reject interrogative complements, while veridical ones such as *be happy*
and *like* accept them. A preferential predicate compares the degree to which its subject prefers
an answer with a threshold set by a comparison class of focus alternatives, and it presupposes
Threshold Significance, that some member of the class clears the threshold. With a question, the
comparison class lies inside the question, so *hope* asserts no more than it presupposes and is
true whenever defined; a meaning [L-analytic in this way](##UegakiSudo2019.isLAnalytic_hope) is
ungrammatical. With a
declarative, and for veridical predicates, which require the preferred answer to be true and
believed, the meaning stays contingent.

## Implementation notes

The non-veridical predicates are the substrate's degree-comparison predicates,
`Preferential.degreeComparison`, and Threshold Significance is `Preferential.ThresholdSignificant`.
A veridical predicate is the same degree comparison applied to the answers that are true and
believed, (26), with belief a predicate parameter. Degrees live in any linear order with two
values. Anand and Hacquard's doxastic condition, (39), the selective focus sensitivity and
exhaustivity refinements of section 4, and the *about*-nominalization of section 5 are not
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

variable {W E D : Type*} [LinearOrder D]

/-! ### L-analyticity for non-veridical preferentials -/

section LAnalytic

variable (V π : (E → W → Set W → D) → (Set (Set W) → D) → Set (Set W) → E → Set (Set W) → W → Prop)

/-- The composition of a predicate `V` with a question, defined where `π` holds, is L-analytic when
it has one truth value under every variable assignment where it is defined, (37a), on the
interrogative skeleton (38b): the assignments give the degree function, threshold, subject, world,
question, and comparison class, which by (29) lies inside the question. -/
def IsLAnalytic : Prop :=
  ∃ t : Prop, ∀ μ θ C x Q w, C ⊆ Q → Q.Nontrivial → π μ θ C x Q w → (V μ θ C x Q w ↔ t)

end LAnalytic

/-- Threshold Significance, (36), as a condition on the assignments of the skeleton. -/
def thresholdSignificance (μ : E → W → Set W → D) (θ : Set (Set W) → D) (C : Set (Set W)) (x : E)
    (_ : Set (Set W)) (w : W) : Prop :=
  ThresholdSignificant (μ x w) θ C

/-- With the comparison class inside the question, the assertion of *hope* with a question is true
whenever its presupposition is, so the meaning is L-analytic, which makes *hope* anti-rogative. -/
theorem isLAnalytic_hope : IsLAnalytic (D := D) (W := W) (E := E) degreeComparison
    thresholdSignificance :=
  ⟨True, fun μ θ C x _ w hCQ _ h ↦
    iff_of_true ((degreeComparison_iff_thresholdSignificant μ θ C hCQ x w).2 h) trivial⟩

/-- *Hope* with a declarative is not trivial (35). -/
theorem exists_significance_not_hope_declarative [Nontrivial D] :
    ∃ (μ : Unit → Bool → Set Bool → D) (θ : Set (Set Bool) → D) (C : Set (Set Bool))
      (A : Set Bool), A ∈ C ∧ Preferential.ThresholdSignificant (μ () true) θ C ∧
        ¬ degreeComparison μ θ C () {A} true := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_lt D
  refine ⟨fun _ _ p ↦ if true ∈ p then b else a, fun _ ↦ a, {{true}, {false}}, {false},
    by simp, ⟨{true}, by simp, by simpa using hab⟩, ?_⟩
  rw [degreeComparison_singleton, mem_preferred]
  simp

/-! ### Veridical preferentials -/

variable (μ : E → W → Set W → D) (θ : Set (Set W) → D) (believes : E → Set W → W → Prop)

/-- A veridical preferential such as *be happy* is the degree comparison over the answers that are
true at the world of evaluation and believed by the subject, (24) and (26). -/
def veridical (C : Set (Set W)) (x : E) (Q : Set (Set W)) (w : W) : Prop :=
  degreeComparison μ θ C x (Q ∩ {p | w ∈ p ∧ believes x p w}) w

/-- Veridical preferentials are clausally distributive, so it is veridicality, not a failure of
distributivity, that lets them take questions. -/
theorem isClausallyDistributive_veridical (C : Set (Set W)) (𝒬 : Set (Set (Set W))) :
    IsClausallyDistributive 𝒬 (veridical μ θ believes C) :=
  .of_forall_iff_exists (fun x p w ↦ (w ∈ p ∧ believes x p w) ∧ p ∈ preferred μ θ C x w)
    fun x Q w ↦ by simp [veridical, degreeComparison, Set.Nonempty, and_assoc]

/-- Veridicality breaks the triviality: under Threshold Significance the assertion still depends on
whether the true answer is the preferred one, so it is not L-analytic. The model has two worlds and
the polar question over them. -/
theorem not_isLAnalytic_veridical [Nontrivial D] :
    ¬ IsLAnalytic (D := D) (W := Bool) (E := Unit)
      (fun μ θ C ↦ veridical μ θ (fun _ _ _ ↦ True) C) thresholdSignificance := by
  classical
  rintro ⟨t, ht⟩
  obtain ⟨a, b, hab⟩ := exists_pair_lt D
  let μ : Unit → Bool → Set Bool → D := fun _ _ p ↦ if true ∈ p then b else a
  let θ : Set (Set Bool) → D := fun _ ↦ a
  let Q : Set (Set Bool) := {{true}, {false}}
  have hQ : Q.Nontrivial := ⟨{true}, by simp [Q], {false}, by simp [Q], by simp⟩
  have hs : ∀ w, thresholdSignificance μ θ Q () Q w := fun _ ↦
    ⟨{true}, by simp [Q], by simpa [μ, θ] using hab⟩
  have ht₁ := (ht μ θ Q () Q true subset_rfl hQ (hs true)).1
    ⟨{true}, ⟨by simp [Q], by simp⟩, by simp [Q], by simpa [μ, θ] using hab⟩
  obtain ⟨p, ⟨hp, hw, -⟩, -, hd⟩ := (ht μ θ Q () Q false subset_rfl hQ (hs false)).2 ht₁
  rcases hp with rfl | rfl
  · simp at hw
  · simp [μ, θ] at hd

end UegakiSudo2019
