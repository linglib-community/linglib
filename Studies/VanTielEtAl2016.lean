module

public import Linglib.Data.Examples.VanTielEtAl2016
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Data.Rat.Defs

/-!
# van Tiel, van Miltenburg, Zevakhina and Geurts (2016): Scalar Diversity

This file formalizes [van-tiel-geurts-2016], which tests the uniformity assumption of the
literature on scalar inferences, that observations about one lexical scale, typically
⟨some, all⟩ or ⟨or, and⟩, generalize to the whole family of scales, `Uniform`. Two experiments
over 43 scales, the rows of `Data.Examples.VanTielEtAl2016`, find that the rate at which the
weaker term gives rise to the upper-bounding inference that the stronger term does not hold
ranges from almost never, ⟨content, happy⟩, to always, ⟨cheap, free⟩, with ⟨some, all⟩ an
extreme case. A scale is a pair of thresholds on a dimension, the terms denoting the degrees
from their threshold up, `LexicalScale`, and the scalar inference is the weak term strengthened
by the negation of the strong one, `upperBounded`. The paper explains the diversity by
distinctness rather than availability: none of four measures of how available the stronger
scalemate is predicts the rates, whereas the two measures of how distinct the scalemates are
do, the rated semantic distance between the terms and boundedness, whether the stronger term
denotes the end point of the dimension, `IsBounded`, in the sense of [rotstein-winter-2004] and
[kennedy-mcnally-2005]. On a bounded scale the terms are told apart on formal grounds alone,
one denoting an interval and the other an end point, `upperBounded_eq_of_isBounded`, which is
why bounded scales license the inference far more often; in the sample boundedness subsumes
the closed grammatical classes, though not in general, ⟨some, most⟩ being open. The two-stage
account of the inference of
[sauerland-2004] and [geurts-2010], from the primary inference that the speaker does not
believe the stronger alternative to the scalar inference by the speaker's competence,
`NeoGricean.compl_Iic_inter_competent`, is considered as a source of the remaining variance and set aside,
since a speaker of *She is pretty* is plausibly opinionated about *beautiful* and the inference
is nonetheless rare.

## Implementation notes

The rates of Experiments 1 and 2, the cloze, frequency, relatedness and distance measures of
Experiments 3 and 4, and the mixed model of Table 5, which explains about half of the variance
with boundedness the largest factor, are reported in the paper and not formalized; the rows
record the scales, their grammatical class and their boundedness. The emotional valence of the
stronger term, Appendix B, does not predict the rates either.

## References

* [van-tiel-geurts-2016]
* [horn-1972]
* [hirschberg-1985]
* [rotstein-winter-2004]
* [kennedy-mcnally-2005]
* [sauerland-2004]
* [geurts-2010]
-/

@[expose] public section

namespace VanTielEtAl2016

/-! ### Lexical scales -/

/-- A lexical scale over a dimension of degrees: the weaker and the stronger term denote the
degrees from a threshold up, the stronger threshold at or above the weaker. -/
structure LexicalScale (D : Type*) [Preorder D] where
  weakThreshold : D
  strongThreshold : D
  le : weakThreshold ≤ strongThreshold

variable {D : Type*} [Preorder D]

namespace LexicalScale

variable (s : LexicalScale D)

/-- The denotation of the weaker term. -/
def weak : Set D := Set.Ici s.weakThreshold

/-- The denotation of the stronger term. -/
def strong : Set D := Set.Ici s.strongThreshold

/-- The stronger term entails the weaker. -/
theorem strong_subset_weak : s.strong ⊆ s.weak := Set.Ici_subset_Ici.2 s.le

/-- The upper-bounding inference: the weaker term strengthened by the negation of the stronger,
the degrees from the weak threshold up to the strong one. -/
def upperBounded : Set D := s.weak \ s.strong

/-- A bounded scale: the stronger term denotes the end point of the dimension. -/
def IsBounded [OrderTop D] : Prop := s.strongThreshold = ⊤

end LexicalScale

theorem LexicalScale.upperBounded_eq_Ico {L : Type*} [LinearOrder L] (s : LexicalScale L) :
    s.upperBounded = Set.Ico s.weakThreshold s.strongThreshold := by
  ext d
  simp [LexicalScale.upperBounded, LexicalScale.weak, LexicalScale.strong, Set.mem_Ico, not_le]

section Bounded

variable {E : Type*} [PartialOrder E] [OrderTop E] (s : LexicalScale E)

/-- On a bounded scale the stronger term denotes the end point alone. -/
theorem LexicalScale.strong_eq_singleton_top (h : s.IsBounded) : s.strong = {⊤} := by
  rw [strong, h, Set.Ici_top]

/-- On a bounded scale the scalemates are told apart on formal grounds alone: the inference
excludes the end point, without inspecting the reach of the stronger term. -/
theorem LexicalScale.upperBounded_eq_of_isBounded (h : s.IsBounded) :
    s.upperBounded = s.weak \ {⊤} := by
  rw [upperBounded, strong_eq_singleton_top s h]

end Bounded

/-! ### Uniformity -/

/-- The uniformity assumption: every scale gives rise to the inference at the same rate. -/
def Uniform {ι : Type*} (rate : ι → ℚ) : Prop := ∀ s t, rate s = rate t

theorem not_uniform_of_ne {ι : Type*} {rate : ι → ℚ} {s t : ι} (h : rate s ≠ rate t) :
    ¬ Uniform rate :=
  fun hu ↦ h (hu s t)

end VanTielEtAl2016
