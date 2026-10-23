module

public import Linglib.Semantics.Degree.Delineation

/-!
# Bochnak (2015): The Degree Semantics Parameter and cross-linguistic variation

Bochnak argues that Washo lacks degree morphology altogether, with no comparatives, measure
phrases, equatives, superlatives or degree adverbs, and analyzes its gradable predicates as
Klein-style vague predicates relative to a comparison class with no degree variable, the negative
setting of Beck's Degree Semantics Parameter. Comparison is a conjoined construction, one clause
asserting the positive and the other denying it, whose truth conditions entail a comparison
through Klein's consistency constraints, the sound and complete delineations of
`Semantics/Degree/Delineation.lean`. Kennedy's two diagnostics of implicit comparison follow:
incompatibility with absolute-standard predicates, and the crisp-judgment effect under the
similarity constraint, stated with van Rooij's margin-of-error order.

## Main statements

* `comparative_ofMeasure_height_iff`: the conjoined comparison closes to Klein's comparative,
  which for a measure-induced delineation is height comparison, with no degree variable.
* `eq24a_bent_straight_fails`, `english_more_bent_succeeds`: on two bent rods every conjoined
  pairing fails where the explicit comparative succeeds.
* `crisp_pair_not_marginOrder`: a minimally different pair defeats implicit comparison at any
  positive margin.
* `cc_b_requires_shared_class`: the comparison entailment needs one comparison class shared by
  both conjuncts.

## References

* [bochnak-2015]
* [beck-2009]
* [klein-1980]
* [kennedy-2007a]
* [kennedy-2007]
* [fara-2000]
* [van-rooij-2011a]
-/

@[expose] public section

namespace Bochnak2015

open Degree

variable {E : Type*}

/-! ### The two lexical shapes ((1), (5))

The paper's proposal is a contrast in lexical type. English *tall* (1) takes
a degree argument for degree morphology to bind; Washo entries (5) are
delineations, `Degree.Delineation E`, with — p. 6:4 — "no
measure function, and no degree variable at all". No Washo constant is
defined: the theorems below quantify over delineations, keeping the
no-measure discipline visible in the types. -/

/-- The degree-based English entry (1) is `[[tall]] = λd λx. height(x) ≥ d`, of type
⟨d,⟨e,t⟩⟩. -/
def tallEnglish (height : E → ℕ) (d : ℕ) (x : E) : Prop :=
  height x ≥ d

/-! ### Conjoined comparison ((14), (27)–(29)) -/

/-- The conjoined comparison (14), with truth conditions (27), holds in context `C` when `x`
counts as G and `y` does not. No comparative morpheme, overt or covert, is involved. -/
def washoConjoined (del : Delineation E) (C : Set E) (x y : E) : Prop :=
  x ∈ del C ∧ y ∉ del C

/-- Klein's existential comparative is the closure of (27) over contexts, since a conjoined
comparison witnesses the discriminating class. -/
theorem washoConjoined_comparative (del : Delineation E) {C : Set E} {x y : E}
    (h : washoConjoined del C x y) : del.Comparative x y :=
  ⟨C, h⟩

/-- Where the target does not count as G, both individuals being short in the paper's context
(29), the conjoined comparison is simply false, so conjoined comparison is obligatorily
norm-related. -/
theorem washoConjoined_norm_related (del : Delineation E) {C : Set E} {x y : E}
    (h : x ∉ del C) :
    ¬ washoConjoined del C x y :=
  fun ⟨hx, _⟩ => h hx

/-- For a measure-induced delineation the closure of (27) coincides with
height comparison — the (28) entailment, through `Delineation.IsSoundFor` and
`Delineation.IsCompleteFor` (the paper's Consistency Constraints in
`Semantics/Degree/Delineation.lean`), with no degree variable in the entry. -/
theorem comparative_ofMeasure_height_iff (height : E → ℕ) (a b : E) :
    (Delineation.ofMeasure height).Comparative a b ↔ height b < height a :=
  Delineation.comparative_ofMeasure_iff height

/-! ### Test 1: absolute standards ((23)–(24))

Two rods, both slightly bent, one more than the other. The English explicit
comparative (23a) is true; each Washo conjoined attempt (24a–c) requires
*straight* or *not bent* to hold of one rod, which is false. -/

section AbsoluteStandard

variable (curvature : E → ℕ) (x y : E)

/-- A minimum-standard predicate such as *bent* or *wet* holds when the measure exceeds the
scale's bottom. The standard is the endpoint, not a comparison class. -/
def bentPred : Prop := curvature x > 0

/-- A maximum-standard predicate such as *straight* or *dry*, the lexical antonym of `bentPred`,
holds when the measure sits at the endpoint. -/
def straightPred : Prop := curvature x = 0

/-- *Bent ∧ straight* (24a) fails, since both rods have nonzero curvature. -/
theorem eq24a_bent_straight_fails (_hx : bentPred curvature x)
    (hy : bentPred curvature y) :
    ¬ (bentPred curvature x ∧ straightPred curvature y) :=
  fun ⟨_, h⟩ => absurd h (Nat.pos_iff_ne_zero.mp hy)

/-- *Bent ∧ ¬bent* (24b) fails, since the second rod is bent too. -/
theorem eq24b_bent_notbent_fails (_hx : bentPred curvature x)
    (hy : bentPred curvature y) :
    ¬ (bentPred curvature x ∧ ¬ bentPred curvature y) :=
  fun ⟨_, h⟩ => h hy

/-- *Straight ∧ ¬straight* (24c) fails, since the first rod is not straight. -/
theorem eq24c_straight_notstraight_fails (hx : bentPred curvature x)
    (_hy : bentPred curvature y) :
    ¬ (straightPred curvature x ∧ ¬ straightPred curvature y) :=
  fun ⟨h, _⟩ => absurd h (Nat.pos_iff_ne_zero.mp hx)

/-- The explicit comparative (23a) succeeds in the same scenario, since any nonzero difference
suffices. -/
theorem english_more_bent_succeeds (hmore : curvature x > curvature y) :
    ∃ d, tallEnglish curvature d x ∧ ¬ tallEnglish curvature d y :=
  ⟨curvature x, le_refl _, by simp [tallEnglish]; omega⟩

end AbsoluteStandard

/-! ### Test 2: crisp judgments and the margin of error ((20)–(22), (58)–(60))

The Similarity Constraint (20) bars separating a minimally-different pair,
so the conjoined form is infelicitous on two nearly-equal ladders (21) —
salvageable with hedges like *wewš* 'almost' (22). The paper's van Rooij
section makes the margin formal: implicit comparison rests on the
margin-of-error order (60), a semi-order (58); explicit comparison is its
`ε = 0` case, the strict weak order (59). -/

section MarginOfError

variable (μ : E → ℕ) (ε : ℕ) {x y z v w : E}

/-- In the margin-of-error order (60), `x` exceeds `y` by more than the margin of error `ε`. -/
def marginOrder (x y : E) : Prop := μ y + ε < μ x

/-- The margin-of-error order is irreflexive (58a). -/
theorem marginOrder_irrefl : ¬ marginOrder μ ε x x := by
  simp [marginOrder]

/-- The margin-of-error order is an interval order (58b). -/
theorem marginOrder_intervalOrder (h₁ : marginOrder μ ε x y)
    (h₂ : marginOrder μ ε v w) :
    marginOrder μ ε x w ∨ marginOrder μ ε v y := by
  simp only [marginOrder] at *; omega

/-- The margin-of-error order is semi-transitive (58c). -/
theorem marginOrder_semitransitive (h₁ : marginOrder μ ε x y)
    (h₂ : marginOrder μ ε y z) (v : E) :
    marginOrder μ ε x v ∨ marginOrder μ ε v z := by
  simp only [marginOrder] at *; omega

theorem marginOrder_zero_iff : marginOrder μ 0 x y ↔ μ y < μ x := by
  simp [marginOrder]

/-- At `ε = 0` the order is almost connected (59c), and so, with irreflexivity and transitivity,
the strict weak order of explicit comparison. -/
theorem marginOrder_zero_almostConnected (h : marginOrder μ 0 x y) (z : E) :
    marginOrder μ 0 x z ∨ marginOrder μ 0 z y := by
  simp only [marginOrder] at *; omega

/-- A minimally different pair never clears a positive margin, the crisp-judgment infelicity of
the conjoined form (21). -/
theorem crisp_pair_not_marginOrder (hε : 1 ≤ ε) (hclose : μ x = μ y + 1) :
    ¬ marginOrder μ ε x y := by
  simp only [marginOrder]; omega

theorem crisp_pair_marginOrder_zero (hclose : μ x = μ y + 1) :
    marginOrder μ 0 x y := by
  simp only [marginOrder]; omega

end MarginOfError

/-! ### Footnote 11: the shared comparison class -/

/-- The (28) entailment requires one comparison class shared by both conjuncts of (27), as
footnote 11 notes. Soundness constrains only same-class separations, so
a delineation sound for `R` can separate `x` from `y` across two distinct
classes while `R x y` fails. -/
theorem cc_b_requires_shared_class :
    ∃ (Entity : Type) (del : Delineation Entity)
      (R : Entity → Entity → Prop),
      del.IsSoundFor R ∧
      ∃ (C₁ C₂ : Set Entity) (x y : Entity), x ∈ del C₁ ∧ y ∉ del C₂ ∧ ¬ R x y := by
  refine ⟨Bool, ⟨fun C ↦ {x | x = true ∧ true ∈ C}⟩, fun a b ↦ a = true ∧ b = false,
    ?_, {true}, {false}, true, true, ⟨rfl, rfl⟩, ?_, ?_⟩
  · rintro C x y ⟨rfl, htC⟩ hneg
    refine ⟨rfl, ?_⟩
    cases y with
    | true => exact absurd ⟨rfl, htC⟩ hneg
    | false => rfl
  · rintro ⟨_, h⟩
    simp at h
  · rintro ⟨_, h⟩
    exact Bool.noConfusion h

end Bochnak2015
