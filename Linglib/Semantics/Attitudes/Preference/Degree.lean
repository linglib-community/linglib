module

public import Linglib.Semantics.Attitudes.Distributivity
public import Mathlib.Data.Set.Insert
public import Mathlib.Order.Interval.Set.Defs

/-!
# Degree semantics for preferential predicates

A preferential predicate such as *hope*, *fear* or *be happy* compares the degree to which its
subject prefers a proposition with a threshold set by a comparison class `C`, in the degree
semantics of Villalta that Romero and Uegaki and Sudo build on. Relating an agent to a set of
propositions, the answers of a question or the singleton of a declarative's proposition, it holds
when some proposition of the set lies in the comparison class and is preferred above the threshold.
The predicate is therefore
[clausally distributive](##Preferential.isClausallyDistributive_degreeComparison),
and when the comparison class lies inside the question [it asserts only that the threshold is
significant on the class](##Preferential.degreeComparison_iff_thresholdSignificant), which is how
Uegaki and Sudo derive the anti-rogativity of *hope*.

## Implementation notes

Degrees live in any linear order. The degree of preference depends on the world of evaluation, as
Uegaki and Sudo's `Pref_w` does; for a negative predicate such as *fear* it measures dispreference.
Which predicates presuppose that the threshold is significant is left to the studies, since
Uegaki and Sudo take all preferentials to and Qing and colleagues only the positive ones.

## References

* [villalta-2008]
* [romero-2015]
* [uegaki-sudo-2019]
-/

@[expose] public section

namespace Preferential

/-- A threshold function `θ` is significant on the comparison class `C` when some member of `C`
measures above `θ C`, [uegaki-sudo-2019] (36): a threshold above the whole class draws no
distinction in it. -/
def ThresholdSignificant {E α : Type*} [Preorder α] (μ : E → α) (θ : Set E → α) (C : Set E) :
    Prop :=
  (C ∩ μ ⁻¹' Set.Ioi (θ C)).Nonempty

variable {W E D : Type*} [LinearOrder D] (μ : E → W → Set W → D) (θ : Set (Set W) → D)
  (C : Set (Set W))

/-- The preferred members of the comparison class `C` for `x` at `w` are those that `x` prefers
at `w` above the threshold of `C`. -/
def preferred (x : E) (w : W) : Set (Set W) :=
  C ∩ (μ x w) ⁻¹' Set.Ioi (θ C)

/-- A degree-comparison predicate relates `x` at `w` to a set of propositions when one of them is
preferred. -/
def degreeComparison (x : E) (Q : Set (Set W)) (w : W) : Prop :=
  (Q ∩ preferred μ θ C x w).Nonempty

variable {μ θ C}

theorem mem_preferred {x : E} {w : W} {p : Set W} :
    p ∈ preferred μ θ C x w ↔ p ∈ C ∧ θ C < μ x w p := Iff.rfl

variable (μ θ C)

/-- With a declarative complement the predicate holds when its proposition is preferred. -/
@[simp] theorem degreeComparison_singleton (x : E) (p : Set W) (w : W) :
    degreeComparison μ θ C x {p} w ↔ p ∈ preferred μ θ C x w := by
  simp [degreeComparison]

/-- Degree-comparison predicates are clausally distributive. -/
theorem isClausallyDistributive_degreeComparison (𝒬 : Set (Set (Set W))) :
    IsClausallyDistributive 𝒬 (degreeComparison μ θ C) :=
  .of_forall_iff_exists (fun x p w ↦ p ∈ preferred μ θ C x w) fun _ _ _ ↦ Iff.rfl

/-- With the comparison class inside the question, a degree-comparison predicate asserts exactly
that the threshold is significant on the class. -/
theorem degreeComparison_iff_thresholdSignificant {Q : Set (Set W)} (hCQ : C ⊆ Q) (x : E)
    (w : W) : degreeComparison μ θ C x Q w ↔ ThresholdSignificant (μ x w) θ C := by
  rw [degreeComparison, preferred, ← Set.inter_assoc, Set.inter_eq_right.2 hCQ]
  rfl

end Preferential
