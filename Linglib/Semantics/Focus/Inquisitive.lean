module

public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Questions.Hamblin.Unrestricted

/-!
# Scalar particles in unrestricted inquisitive semantics

This file defines the propositions that *at least* and *at most* raise in unrestricted
inquisitive semantics. The alternatives are indexed and ranked as for `Focus.atLeast` and
`Focus.atMost`. *At least `i`* raises the content of each alternative at least as strong as `i`
as a possibility, and *at most `i`* raises the content of each alternative at most as strong,
cut down to the worlds where no stronger alternative is true. The unions of these possibilities
are the classical meanings, so the inquisitive entries add only the possibilities they draw
attention to.

## Main definitions

* `Inquisitive.Unrestricted.atLeast`: the possibilities that *at least `i`* raises.
* `Inquisitive.Unrestricted.atMost`: the possibilities that *at most `i`* raises.

## Main results

* `Inquisitive.Unrestricted.sUnion_atLeast`: the informative content of *at least* is
  `Focus.atLeast`.
* `Inquisitive.Unrestricted.sUnion_atMost`: the informative content of *at most* is `Focus.atMost`
  within the union of the alternatives.
* `Inquisitive.Unrestricted.atMost_of_pairwiseDisjoint`: on disjoint alternatives the cut does
  nothing.
* `Inquisitive.Unrestricted.subsingleton_restrict_atLeast`: a speaker who knows that no stronger
  alternative is true restricts *at least* to at most one possibility.
* `Inquisitive.Unrestricted.not_interactiveSincerity_of_only`: a speaker who knows *only `i`*
  cannot sincerely say *at least `i`*.
* `Inquisitive.Unrestricted.sUnion_exh_atLeast`: exhaustifying the possibilities of *at least `p`*
  leaves their union equal to `p`.

## Implementation notes

The prejacent is one alternative. [coppock-brochhagen-2013] also give *at least* an inquisitive
prejacent, collecting the alternatives at least as strong as one of its possibilities; that is the
union of `atLeast` over those possibilities. Their entries are sets of choice functions, which
applied pointwise yield the sets of possibilities defined here.

## References

* [coppock-brochhagen-2013]
* [coppock-beaver-2014]
* [ciardelli-groenendijk-roelofsen-2009]
-/

@[expose] public section

namespace Inquisitive.Unrestricted

open Set Exhaustification

variable {ι W : Type*}

section Defs

variable (S : ι → ι → Prop) (C : Set ι) (P : ι → Set W) (i : ι)

/-- *At least `i`* raises the content of every alternative in `C` at least as strong as `i` on
the scale `S` ([coppock-brochhagen-2013], (52)). -/
def atLeast : Set (Set W) := P '' {j ∈ C | S j i}

/-- *At most `i`* raises the content of every alternative in `C` at most as strong as `i`, cut
down to the worlds where no stronger alternative is true ([coppock-brochhagen-2013], (60)). -/
def atMost : Set (Set W) := (· ∩ Focus.atMost S C P i) '' (P '' {j ∈ C | S i j})

end Defs

variable {S : ι → ι → Prop} {C : Set ι} {P : ι → Set W} {i : ι} {k : Set W}

/-! ### Informative content -/

/-- The informative content of inquisitive *at least* is the classical *at least*. -/
theorem sUnion_atLeast : ⋃₀ atLeast S C P i = Focus.atLeast S C P i := by
  ext w
  simp only [atLeast, sUnion_image, mem_iUnion, mem_ofPred_eq, exists_prop, Focus.mem_atLeast]
  exact ⟨fun ⟨j, ⟨hj, hs⟩, hw⟩ ↦ ⟨j, hj, hw, hs⟩, fun ⟨j, hj, hw, hs⟩ ↦ ⟨j, ⟨hj, hs⟩, hw⟩⟩

/-- The informative content of inquisitive *at most* is the classical *at most* within the union
of the alternatives. -/
theorem sUnion_atMost : ⋃₀ atMost S C P i = Focus.atMost S C P i ∩ ⋃ j ∈ C, P j := by
  ext w
  simp only [atMost, image_image, sUnion_image, mem_iUnion, mem_ofPred_eq, mem_inter_iff,
    exists_prop]
  constructor
  · rintro ⟨j, ⟨hj, _⟩, hw, hmax⟩
    exact ⟨hmax, j, hj, hw⟩
  · rintro ⟨hmax, j, hj, hw⟩
    exact ⟨j, ⟨hj, hmax j hj hw⟩, hw, hmax⟩

/-- On pairwise disjoint alternatives, *at most `i`* raises the alternatives at most as strong as
`i` unchanged. -/
theorem atMost_of_pairwiseDisjoint (h : C.PairwiseDisjoint P) :
    atMost S C P i = P '' {j ∈ C | S i j} := by
  rw [atMost, image_image]
  refine image_congr fun j ⟨hj, hij⟩ ↦ inter_eq_left.2 fun w hw j' hj' hw' ↦ ?_
  rwa [h.elim_set hj' hj w hw' hw]

/-- When no alternative includes another, *at least* is not attentive. -/
theorem not_isAttentive_atLeast (h : IsAntichain (· ⊆ ·) (range P)) :
    ¬ IsAttentive (atLeast S C P i) :=
  not_isAttentive_iff.2 (h.subset (image_subset_range _ _))

/-! ### Ordered alternatives -/

section Preorder

variable [Preorder ι] {a b : ι}

theorem atLeast_ge_univ (a : ι) : atLeast (· ≥ ·) univ P a = P '' Ici a := by
  rw [atLeast]; congr 1; ext; simp

theorem atMost_ge_univ (a : ι) :
    atMost (· ≥ ·) univ P a = (· ∩ Focus.atMost (· ≥ ·) univ P a) '' (P '' Iic a) := by
  rw [atMost]; congr 2; ext; simp

/-- *At least `a`* is attentive when a stronger alternative strictly entails `a`. -/
theorem isAttentive_atLeast_ge (hab : a ≤ b) (h : P b ⊂ P a) :
    IsAttentive (atLeast (· ≥ ·) univ P a) := by
  rw [atLeast_ge_univ]
  exact isAttentive_of_ssubset (mem_image_of_mem _ hab) (mem_image_of_mem _ self_mem_Ici) h

end Preorder

/-! ### Ignorance -/

/-- A speaker who knows that no alternative stronger than `i` is true restricts *at least `i`* to
at most one possibility. -/
theorem subsingleton_restrict_atLeast [Std.Antisymm S] (hk : k ⊆ Focus.atMost S C P i) :
    (restrict (atLeast S C P i) k).Subsingleton := by
  have key : ∀ p ∈ atLeast S C P i, (k ∩ p).Nonempty → p = P i := by
    rintro _ ⟨j, ⟨hj, hji⟩, rfl⟩ ⟨w, hwk, hwj⟩
    rw [antisymm hji (hk hwk j hj hwj)]
  exact subsingleton_restrict_iff.2 fun p hp q hq hkp hkq ↦ by rw [key p hp hkp, key q hq hkq]

/-- A speaker who knows *only `i`* cannot sincerely say *at least `i`* when that raises several
possibilities. -/
theorem not_interactiveSincerity_of_only [Std.Antisymm S]
    (hk : ∀ w ∈ k, Focus.only S C P i w = .true) (hi : (atLeast S C P i).Nontrivial) :
    ¬ InteractiveSincerity (atLeast S C P i) k :=
  not_interactiveSincerity hi
    (subsingleton_restrict_atLeast fun w hw ↦ (Focus.only_eq_true_iff.1 (hk w hw)).2)

/-! ### Exhaustification -/

/-- Exhaustifying each possibility that *at least `p`* raises against the alternatives leaves
their union equal to `p`, when each world of `p` has a strongest true alternative. -/
theorem sUnion_exh_atLeast {C : Set (Set W)} {p : Set W} (hp : p ∈ C)
    (h : ∀ w ∈ p, ∃ q, IsLeast {q ∈ C | w ∈ q} q) :
    ⋃₀ (exh C '' atLeast (· ⊆ ·) C id p) = p := by
  refine Subset.antisymm (sUnion_subset ?_) fun w hw ↦ ?_
  · rintro _ ⟨_, ⟨q, ⟨-, hqp⟩, rfl⟩, rfl⟩
    exact (exh_subset C q).trans hqp
  · obtain ⟨q, hq⟩ := h w hw
    exact ⟨_, ⟨q, ⟨q, ⟨hq.1.1, hq.2 ⟨hp, hw⟩⟩, rfl⟩, rfl⟩, (mem_exh_iff_isLeast_of_mem hq.1.1).2 hq⟩

end Inquisitive.Unrestricted
