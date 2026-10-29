module

public import Linglib.Core.Order.IntervalOrder
public import Linglib.Semantics.Degree.Delineation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Comparable
public import Mathlib.Tactic.Linarith
public import Studies.Kennedy2007

/-!
# Bochnak (2015): The Degree Semantics Parameter and cross-linguistic variation

Washo lacks degree morphology, and Bochnak analyzes its gradable predicates as delineations with
no degree argument, the negative setting of the Degree Semantics Parameter of Beck and colleagues.
Its conjoined comparison, *x is tall, y is not tall*, [entails the
comparison](##conjoinedComparison_entails) under Klein's consistency constraints, provided [the
conjuncts share a comparison class](##exists_classes_iff). It is implicit comparison: unlike the
English comparative it fails [with absolute-standard predicates](##eq24_fails) and [on a crisp
pair](##crisp_judgment), and under the Similarity Constraint it [requires a difference beyond a
margin of error](##marginOrder_of_conjoinedComparison), van Rooij's semi-order.

## Implementation notes

* No Washo entry is defined: the paper's entry (5) has no measure function, so the theorems
  quantify over delineations. The English entry (1) and the degree morphemes (2) take a measure
  into any linear order.
* *y is not G* is true where `y` is in the negative extension of the delineation, so the
  conjoined comparison (27), the Consistency Constraint (28b) (`Delineation.IsSoundFor`) and the
  Similarity Constraint (20), which bars judging *x is G* true and *y is G* false, are stated with
  it.
* An absolute-standard predicate has one extension in every comparison class. The extensions of
  *bent* and *straight* are stated with Kennedy's minimum and maximum standards on a scale of
  bend, which describe the model and not the entries, as the paper's degree-free relative/absolute
  distinction requires.
* The Similarity Constraint is a condition on a delineation for a relation of similarity, imposed
  in every comparison class containing the similar pair; so imposed it is a tolerance condition,
  which a class of many small steps meets only trivially. For the margin of error, similarity is
  incomparability under the margin order, and the margin is real-valued as in measurement theory.
* The library has interval orders, `IsIntervalOrder`, but no class of semi-orders, so
  semi-transitivity (58c) is a theorem of its own.

## References

* [bochnak-2015]
* [beck-2009]
* [klein-1980]
* [kennedy-mcnally-2005]
* [kennedy-2007a]
* [kennedy-2007]
* [fara-2000]
* [van-rooij-2011a]
-/

@[expose] public section

namespace Bochnak2015

open Degree Delineation

variable {E D : Type*}

/-! ### Degree arguments ((1)–(3)) -/

section DegreeArgument

variable [LinearOrder D] (μ : E → D)

/-- The English entry (1) of a gradable predicate measured by `μ` takes a degree argument,
`⟦tall⟧ = λd λx. height(x) ⪰ d`. -/
def GradablePredicate (d : D) (x : E) : Prop :=
  d ≤ μ x

/-- A degree morpheme (2) binds the degree argument of `G` under a restriction `R`,
`⟦Deg⟧ = λG λx. ∃d[R(d) ∧ G(d)(x)]`, after Kennedy and McNally. -/
def Deg (R : D → Prop) (G : D → E → Prop) (x : E) : Prop :=
  ∃ d, R d ∧ G d x

-- the comparative at `θ = μ y` and *pos* (3) at the contextual standard `θ = s_G`
theorem deg_lt_iff {θ : D} {x : E} : Deg (θ < ·) (GradablePredicate μ) x ↔ θ < μ x :=
  ⟨fun ⟨_, hθ, hd⟩ ↦ hθ.trans_le hd, fun h ↦ ⟨μ x, h, le_rfl⟩⟩

end DegreeArgument

/-! ### Conjoined comparison ((26)–(29), (32)) -/

section Conjoined

variable {del : Delineation E} {C : Set E} {x y : E}

/-- The conjoined comparison (26), with truth conditions (27), holds in context `C` when `x`
counts as G and `y` counts as not G. No comparative morpheme, overt or covert, is involved. -/
def ConjoinedComparison (del : Delineation E) (C : Set E) (x y : E) : Prop :=
  x ∈ del C ∧ y ∈ del.neg C

/-- Under the second Consistency Constraint (28b) the truth conditions (27) entail the comparison,
which the conjoined comparison does not assert. -/
theorem conjoinedComparison_entails {R : E → E → Prop} (hs : del.IsSoundFor R)
    (h : ConjoinedComparison del C x y) : R x y :=
  hs C x y h.1 h.2

-- (29)
theorem not_conjoinedComparison_of_not_mem (h : x ∉ del C) : ¬ ConjoinedComparison del C x y :=
  fun hc ↦ h hc.1

-- (32)
theorem comparative_not_normRelated [LinearOrder D] (μ : E → D) {s : D} (hlt : μ y < μ x)
    (hs : μ x ≤ s) :
    Deg (μ y < ·) (GradablePredicate μ) x ∧ ¬ Deg (s < ·) (GradablePredicate μ) x ∧
      ¬ Deg (s < ·) (GradablePredicate μ) y := by
  simp only [deg_lt_iff, not_lt]
  exact ⟨hlt, hs, hlt.le.trans hs⟩

/-- The comparison needs one comparison class shared by both conjuncts (footnote 11). With two
classes the conjunction says nothing about `y`: under the delineation of a measure, which meets
both Consistency Constraints, it holds exactly when something measures below `x`. -/
theorem exists_classes_iff [LinearOrder D] (μ : E → D) :
    (∃ C₁ C₂, x ∈ ofMeasure μ C₁ ∧ y ∈ (ofMeasure μ).neg C₂) ↔ ∃ z, μ z < μ x :=
  ⟨fun ⟨_, _, ⟨z, _, hz⟩, _⟩ ↦ ⟨z, hz⟩, fun ⟨z, hz⟩ ↦ ⟨{z}, ∅, ⟨z, rfl, hz⟩, by simp⟩⟩

end Conjoined

/-! ### Absolute standards ((23)–(24))

Two rods are both slightly bent, one more than the other. The standard of *bent* or *straight* is
an endpoint of the scale whatever the context, so a conjoined comparison is false except in the
limiting case where one rod has no bend at all. -/

section AbsoluteStandard

variable [LinearOrder D] [OrderBot D] (μ : E → D) {C : Set E} {x y : E}

/-- An absolute-standard predicate has the same extension `S` in every comparison class. -/
def absolute (S : Set E) : Delineation E :=
  ofExtension fun _ ↦ S

/-- *Bent*, whose extension is the minimum standard on a scale of bend `μ`. -/
abbrev bent : Delineation E :=
  absolute (μ ⁻¹' Set.Ioi ⊥)

/-- *Straight*, whose extension is the maximum standard on the reversed scale. -/
abbrev straight : Delineation E :=
  absolute ((OrderDual.toDual ∘ μ) ⁻¹' Set.Ici ⊤)

theorem mem_straight_iff : x ∈ straight μ C ↔ x ∉ bent μ C := by
  change x ∈ (OrderDual.toDual ∘ μ) ⁻¹' Set.Ici ⊤ ↔ x ∈ (μ ⁻¹' Set.Ioi ⊥)ᶜ
  rw [(Kennedy2007.antonyms_isCompl μ).compl_eq]

theorem conjoinedComparison_bent_iff : ConjoinedComparison (bent μ) C x y ↔ ⊥ < μ x ∧ μ y = ⊥ := by
  simp [ConjoinedComparison, absolute]

theorem conjoinedComparison_straight_iff :
    ConjoinedComparison (straight μ) C x y ↔ μ x = ⊥ ∧ ⊥ < μ y := by
  have hneg : y ∈ (straight μ).neg C ↔ y ∈ bent μ C := by
    change y ∉ straight μ C ↔ _
    rw [mem_straight_iff, not_not]
  rw [ConjoinedComparison, mem_straight_iff, hneg]
  simp [absolute]

/-- In the context of (23), with both rods bent and `x` more bent than `y`, the explicit
comparative (23a) holds, while each conjoined attempt (24a–c) needs one rod to be straight or not
bent and fails. -/
theorem eq24_fails (hy : ⊥ < μ y) (hlt : μ y < μ x) :
    Deg (μ y < ·) (GradablePredicate μ) x ∧ ¬ (x ∈ bent μ C ∧ y ∈ straight μ C) ∧
      ¬ ConjoinedComparison (bent μ) C x y ∧ ¬ ConjoinedComparison (straight μ) C x y := by
  refine ⟨(deg_lt_iff μ).2 hlt, ?_, ?_, ?_⟩
  · rw [mem_straight_iff]
    exact fun h ↦ hy.ne' ((conjoinedComparison_bent_iff μ).1 h).2
  · exact fun h ↦ hy.ne' ((conjoinedComparison_bent_iff μ).1 h).2
  · exact fun h ↦ (hy.trans hlt).ne' ((conjoinedComparison_straight_iff μ).1 h).1

end AbsoluteStandard

/-! ### Crisp judgments and the margin of error ((20)–(21), (58)–(60))

The Similarity Constraint (20) bars separating two entities that differ only to a very small
degree, so a conjoined comparison of two nearly equal ladders (21) is infelicitous, while the
English comparative needs only a nonzero difference. Van Rooij's margin-of-error order (60) is a
semi-order (58) and, with no margin, a strict weak order (59), the order of the measure. -/

section CrispJudgment

/-- The Similarity Constraint (20) on a delineation, for a relation `sim` of differing only to a
very small degree: no comparison class containing two similar entities puts one in the positive
and the other in the negative extension. -/
def SimilarityConstraint (del : Delineation E) (sim : E → E → Prop) : Prop :=
  ∀ C, ∀ x ∈ C, ∀ y ∈ C, sim x y → x ∈ del C → y ∉ del.neg C

variable (μ : E → ℝ) (ε : ℝ) {del : Delineation E} {C : Set E} {x y z : E}

/-- In the margin-of-error order (60), `x` exceeds `y` by more than the margin of error `ε`. -/
def MarginOrder (x y : E) : Prop :=
  μ y + ε < μ x

variable {μ ε}

@[simp] theorem marginOrder_zero_iff : MarginOrder μ 0 x y ↔ μ y < μ x := by
  simp [MarginOrder]

-- (21)
theorem not_conjoinedComparison_of_similar {sim : E → E → Prop} (h : SimilarityConstraint del sim)
    (hx : x ∈ C) (hy : y ∈ C) (hs : sim x y) : ¬ ConjoinedComparison del C x y :=
  fun hc ↦ h C x hx y hy hs hc.1 hc.2

/-- In a crisp-judgment context (21), where `x` exceeds `y` by no more than the margin of error,
the English comparative holds while no conjoined comparison obeying the Similarity Constraint
does. -/
theorem crisp_judgment (hsim : SimilarityConstraint del (IncompRel (MarginOrder μ ε)))
    (hx : x ∈ C) (hy : y ∈ C) (hlt : μ y < μ x) (hclose : μ x ≤ μ y + ε) :
    Deg (μ y < ·) (GradablePredicate μ) x ∧ ¬ ConjoinedComparison del C x y :=
  ⟨(deg_lt_iff μ).2 hlt, not_conjoinedComparison_of_similar hsim hx hy
    ⟨hclose.not_gt, fun h ↦ by unfold MarginOrder at h; linarith⟩⟩

/-- Under the Similarity Constraint for the margin of error and the second Consistency Constraint
for the measure, a conjoined comparison entails the margin-of-error order (60): its first entity
exceeds the second by more than the margin. -/
theorem marginOrder_of_conjoinedComparison (hε : 0 ≤ ε) (hs : del.IsSoundFor fun a b ↦ μ b < μ a)
    (hsim : SimilarityConstraint del (IncompRel (MarginOrder μ ε))) (hx : x ∈ C) (hy : y ∈ C)
    (h : ConjoinedComparison del C x y) : MarginOrder μ ε x y := by
  by_contra hn
  refine not_conjoinedComparison_of_similar hsim hx hy ⟨hn, fun h' ↦ ?_⟩ h
  have := conjoinedComparison_entails hs h
  unfold MarginOrder at h'
  linarith

variable (μ) in
-- (58a), (58b)
theorem isIntervalOrder_marginOrder (hε : 0 ≤ ε) : IsIntervalOrder E (MarginOrder μ ε) where
  irrefl x h := by unfold MarginOrder at h; linarith
  two_plus_two x y v w h₁ h₂ := by
    unfold MarginOrder at *
    by_contra! h
    linarith [h.1, h.2]

-- (58c)
theorem marginOrder_semitransitive (h₁ : MarginOrder μ ε x y) (h₂ : MarginOrder μ ε y z)
    (v : E) : MarginOrder μ ε x v ∨ MarginOrder μ ε v z := by
  unfold MarginOrder at *
  by_contra! h
  linarith [h.1, h.2]

variable (μ) in
-- (59c)
theorem isOrderConnected_marginOrder_zero : IsOrderConnected E (MarginOrder μ 0) :=
  ⟨fun a b c h ↦ by
    simp only [marginOrder_zero_iff] at *
    exact (lt_or_ge (μ b) (μ a)).imp_right h.trans_le⟩

variable (μ) in
-- (59)
theorem isStrictWeakOrder_marginOrder_zero : IsStrictWeakOrder E (MarginOrder μ 0) :=
  haveI : Std.Asymm (MarginOrder μ 0) :=
    ⟨fun a b h h' ↦ by simp only [marginOrder_zero_iff] at h h'; exact h.not_gt h'⟩
  haveI := isOrderConnected_marginOrder_zero μ
  isStrictWeakOrder_of_isOrderConnected

-- (60): with a positive margin the order is no weak order
theorem not_isOrderConnected_marginOrder (hε : 0 < ε) :
    ¬ IsOrderConnected ℝ (MarginOrder id ε) := fun h ↦ by
  have := h.conn (2 * ε) ε 0 (by simp only [MarginOrder, id]; linarith)
  simp only [MarginOrder, id] at this
  rcases this with h | h <;> linarith

end CrispJudgment

end Bochnak2015
