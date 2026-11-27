module

public import Linglib.Core.Order.IntervalOrder
public import Linglib.Semantics.Degree.Sorites
public import Linglib.Semantics.Delineation
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
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
* An absolute-standard predicate has one standard in every comparison class. *Bent* and
  *straight* are the delineations of a scale of bend at Kennedy's minimum and maximum standards,
  which describe the model and not the entries, as the paper's degree-free relative/absolute
  distinction requires.
* The Similarity Constraint is a condition on a delineation for a relation of similarity, imposed
  in every comparison class containing the similar pair. On a gapless delineation it is the
  tolerance premise of a soritical argument along similarity within the class, so a conjoined
  comparison holds of no two members joined by a chain of similar members; a class that contains
  the whole interval between two measures admits none. In the paper's exposition of van Rooij the
  constraint is evaluated in the class of the two compared individuals, and further members of a
  class obviate it. For the margin of error, similarity is incomparability under the margin order,
  and the margin is real-valued as in measurement theory.
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

open Delineation

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

/-- *Bent* takes the minimum standard on a scale of bend `μ` in every comparison class. -/
abbrev bent : Delineation E :=
  ofStandard μ fun _ ↦ .Ioi ⊥

/-- *Straight* takes the maximum standard on the reversed scale in every comparison class. -/
abbrev straight : Delineation E :=
  ofStandard (OrderDual.toDual ∘ μ) fun _ ↦ .Ici ⊤

theorem mem_straight_iff : x ∈ straight μ C ↔ x ∉ bent μ C := by
  change x ∈ (OrderDual.toDual ∘ μ) ⁻¹' Set.Ici ⊤ ↔ x ∈ (μ ⁻¹' Set.Ioi ⊥)ᶜ
  rw [(Kennedy2007.antonyms_isCompl μ).compl_eq]

theorem conjoinedComparison_bent_iff : ConjoinedComparison (bent μ) C x y ↔ ⊥ < μ x ∧ μ y = ⊥ := by
  simp [ConjoinedComparison, ofStandard]

theorem conjoinedComparison_straight_iff :
    ConjoinedComparison (straight μ) C x y ↔ μ x = ⊥ ∧ ⊥ < μ y := by
  have hneg : y ∈ (straight μ).neg C ↔ y ∈ bent μ C := by
    change y ∉ straight μ C ↔ _
    rw [mem_straight_iff, not_not]
  rw [ConjoinedComparison, mem_straight_iff, hneg]
  simp [ofStandard]

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

-- on a gapless delineation the Similarity Constraint says that the positive extension of every
-- class is tolerant along similarity within the class
theorem similarityConstraint_iff_tolerance {del : Delineation E} {sim : E → E → Prop}
    (hd : del.IsGapless) : SimilarityConstraint del sim ↔
      ∀ C, ∀ ⦃x y⦄, x ∈ del C → (x ∈ C ∧ y ∈ C ∧ sim x y) → y ∈ del C := by
  simp only [SimilarityConstraint, hd.mem_neg_iff, not_not]
  exact forall_congr' fun C ↦ ⟨fun h x y hx ⟨hxC, hyC, hs⟩ ↦ h x hxC y hyC hs hx,
    fun h x hxC y hyC hs hx ↦ h hx ⟨hxC, hyC, hs⟩⟩

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

-- under the Similarity Constraint a conjoined comparison in a gapless delineation is a Sorites
theorem ConjoinedComparison.sorites {sim : E → E → Prop} (hd : del.IsGapless)
    (hsim : SimilarityConstraint del sim) (h : ConjoinedComparison del C x y) :
    Sorites (· ∈ del C) (fun a b ↦ a ∈ C ∧ b ∈ C ∧ sim a b) x y :=
  ⟨h.1, (similarityConstraint_iff_tolerance hd).1 hsim C, hd.mem_neg_iff.1 h.2⟩

-- under the Similarity Constraint a gapless delineation admits no conjoined comparison of two
-- members of a class joined by a chain of similar members of the class
theorem not_conjoinedComparison_of_reflTransGen {sim : E → E → Prop} (hd : del.IsGapless)
    (hsim : SimilarityConstraint del sim)
    (hxy : Relation.ReflTransGen (fun a b ↦ a ∈ C ∧ b ∈ C ∧ sim a b) x y) :
    ¬ ConjoinedComparison del C x y :=
  fun h ↦ (h.sorites hd hsim).not_reflTransGen hxy

private theorem reflTransGen_incompRel_marginOrder {C : Set ℝ} (hε : 0 < ε) (n : ℕ) :
    ∀ {x y : ℝ}, y ≤ x → x - y ≤ n * ε → Set.Icc y x ⊆ C → Relation.ReflTransGen
      (fun a b ↦ a ∈ C ∧ b ∈ C ∧ IncompRel (MarginOrder id ε) a b) x y := by
  have key (a b : ℝ) (h₁ : a ≤ b + ε) (h₂ : b ≤ a + ε) : IncompRel (MarginOrder id ε) a b :=
    ⟨fun h ↦ by simp only [MarginOrder, id] at h; linarith,
      fun h ↦ by simp only [MarginOrder, id] at h; linarith⟩
  induction n with
  | zero =>
    intro x y hyx h _
    obtain rfl : x = y := le_antisymm (by simpa using h) hyx
    exact .refl
  | succ n ih =>
    intro x y hyx h hC
    rcases le_total (x - y) ε with hle | hle
    · exact .single ⟨hC ⟨hyx, le_rfl⟩, hC ⟨le_rfl, hyx⟩, key x y (by linarith) (by linarith)⟩
    · have hx : x - ε ∈ Set.Icc y x := ⟨by linarith, by linarith⟩
      refine .head ⟨hC ⟨hyx, le_rfl⟩, hC hx, key x (x - ε) (by linarith) (by linarith)⟩
        (ih hx.1 (by push_cast at h; linarith) fun z hz ↦ hC ⟨hz.1, hz.2.trans hx.2⟩)

-- under the Similarity Constraint for a positive margin of error a gapless delineation of the
-- reals admits no conjoined comparison in a class containing every measure between the two
theorem not_conjoinedComparison_of_Icc_subset {del : Delineation ℝ} {C : Set ℝ} {x y : ℝ}
    (hd : del.IsGapless) (hε : 0 < ε)
    (hsim : SimilarityConstraint del (IncompRel (MarginOrder id ε))) (hyx : y ≤ x)
    (hC : Set.Icc y x ⊆ C) : ¬ ConjoinedComparison del C x y := by
  obtain ⟨n, hn⟩ := exists_nat_ge ((x - y) / ε)
  exact not_conjoinedComparison_of_reflTransGen hd hsim
    (reflTransGen_incompRel_marginOrder hε n hyx ((div_le_iff₀ hε).1 hn) hC)

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
