/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Variety.Definite`.
-/
module

public import Linglib.Core.Algebra.Group.Idempotent
public import Linglib.Core.Computability.Definite
public import Linglib.Core.Computability.Variety.Basic

/-!
# Definite languages and the pseudovarieties **D**, **K** and **LI**

This file proves the Eilenberg correspondences for the definite languages and their relatives.
Over a finite alphabet, the definite, reverse definite and generalized definite languages are
exactly the regular languages whose syntactic semigroup lies in the pseudovariety **D**, **K** and
**LI** respectively, and the finite or cofinite languages are those whose syntactic semigroup lies
in both **D** and **K**. Both directions pass through a window characterization in the syntactic
monoid: `L` is `k`-definite exactly when the class of every word of length at least `k` is a right
zero, and similarly for the other two classes.

## Implementation notes

The bound `|S|` and the route through long products follow Chapter XIV of Pin's lecture notes. The
window conditions range over words of length at least `k` rather than over the whole syntactic
monoid, because the pseudovarieties are varieties of semigroups and do not see the empty word.

## References

* [perles-rabin-shamir-1963]
* [eilenberg-1976]
* [pin-mfa]
-/

public section

namespace Language

variable {α : Type*} {L : Language α} {k : ℕ}

/-! ### Window characterizations -/

private theorem takeAt_append_middle (e : Edge) {u v : List α} (h : e.takeAt k u = e.takeAt k v)
    (x y : List α) : e.takeAt k (x ++ u ++ y) = e.takeAt k (x ++ v ++ y) :=
  e.takeAt_append_congr (e.takeAt_append_congr_right h x) y

/-! #### Definite languages -/

theorem IsDefinite.syntacticClass_append_left (h : L.IsDefinite k) {u : List α}
    (hu : k ≤ u.length) (t : List α) : L.syntacticClass (t ++ u) = L.syntacticClass u :=
  syntacticClass_eq_iff.2 fun x y ↦
    iff_of_eq (h (takeAt_append_middle .right (List.rtake_append_of_le_length hu) x y))

theorem IsDefinite.isRightZero_syntacticClass (h : L.IsDefinite k) {u : List α}
    (hu : k ≤ u.length) : IsRightZero (L.syntacticClass u) := fun m ↦ by
  obtain ⟨t, rfl⟩ := L.syntacticClass_surjective m
  rw [← syntacticClass_append]
  exact h.syntacticClass_append_left hu t

/-- A language is `k`-definite exactly when the syntactic class of every word of length at least
`k` is a right zero of the syntactic monoid. -/
theorem isDefinite_iff_forall_isRightZero_syntacticClass :
    L.IsDefinite k ↔ ∀ u : List α, k ≤ u.length → IsRightZero (L.syntacticClass u) := by
  refine ⟨fun h _ ↦ h.isRightZero_syntacticClass, fun h ↦ isDefinite_iff_mem_takeAt.2 fun w ↦ ?_⟩
  rcases le_or_gt k w.length with hw | hw
  · refine mem_iff_of_syntacticClass_eq ?_
    conv_lhs => rw [← List.rdrop_append_rtake w k]
    rw [syntacticClass_append, Edge.takeAt_right,
      h _ (by rw [List.length_rtake]; omega)]
  · rw [Edge.takeAt_right, List.rtake_of_length_le hw.le]

/-! #### Reverse definite languages -/

private theorem isRightZero_syntacticClass_reverse {u : List α} :
    IsRightZero (L.reverse.syntacticClass u.reverse) ↔ IsLeftZero (L.syntacticClass u) := by
  simp only [isRightZero_iff, isLeftZero_iff, (syntacticClass_surjective _).forall,
    ← syntacticClass_append, syntacticClass_reverse_eq_iff, List.reverse_append,
    List.reverse_reverse]
  exact (List.reverse_involutive.surjective.forall
    (p := fun t ↦ L.syntacticClass (u ++ t) = L.syntacticClass u)).symm

/-- The window for the reverse definite languages is the window for the definite ones, through
reversal. -/
theorem isReverseDefinite_iff_forall_isLeftZero_syntacticClass :
    L.IsReverseDefinite k ↔ ∀ u : List α, k ≤ u.length → IsLeftZero (L.syntacticClass u) := by
  rw [isReverseDefinite_iff_isDefinite_reverse, isDefinite_iff_forall_isRightZero_syntacticClass,
    List.reverse_involutive.surjective.forall]
  simp only [List.length_reverse, isRightZero_syntacticClass_reverse]

theorem IsReverseDefinite.isLeftZero_syntacticClass (h : L.IsReverseDefinite k) {u : List α}
    (hu : k ≤ u.length) : IsLeftZero (L.syntacticClass u) :=
  isReverseDefinite_iff_forall_isLeftZero_syntacticClass.1 h u hu

/-! #### Generalized definite languages -/

theorem IsGeneralizedDefinite.syntacticClass_mul_mul_self (h : L.IsGeneralizedDefinite k)
    {u : List α} (hu : k ≤ u.length) (s : L.SyntacticMonoid) :
    L.syntacticClass u * s * L.syntacticClass u = L.syntacticClass u := by
  obtain ⟨t, rfl⟩ := L.syntacticClass_surjective s
  rw [← syntacticClass_append, ← syntacticClass_append]
  exact syntacticClass_eq_iff.2 fun x y ↦ isGeneralizedDefinite_iff_edges.1 h
    (takeAt_append_middle .left ((congrArg _ (List.append_assoc u t u)).trans
      (List.take_append_of_le_length hu)) x y)
    (takeAt_append_middle .right (List.rtake_append_of_le_length hu) x y)

theorem isGeneralizedDefinite_iff_forall_syntacticClass_mul_mul_self :
    L.IsGeneralizedDefinite k ↔ ∀ u : List α, k ≤ u.length → ∀ s,
      L.syntacticClass u * s * L.syntacticClass u = L.syntacticClass u := by
  refine ⟨fun h _ ↦ h.syntacticClass_mul_mul_self, fun h ↦ ?_⟩
  refine isGeneralizedDefinite_iff_edges.2 fun a b hpre hsuf ↦ mem_iff_of_syntacticClass_eq ?_
  rw [Edge.takeAt_left, Edge.takeAt_left] at hpre
  rw [Edge.takeAt_right, Edge.takeAt_right] at hsuf
  have hlen : min k a.length = min k b.length := by
    simpa only [List.length_take] using congrArg List.length hpre
  rcases le_or_gt k a.length with ha | ha
  · -- `[a] = [a] * [b] = [b]`: the shared prefix absorbs `[a]` on the left, the shared suffix
    -- absorbs `[b]` on the right.
    have hp := h (a.take k) (by rw [List.length_take]; omega)
    have hq := h (a.rtake k) (by rw [List.length_rtake]; omega)
    have ha₁ := List.take_append_drop k a
    have hb₁ : a.take k ++ b.drop k = b := hpre ▸ List.take_append_drop k b
    have ha₂ := List.rdrop_append_rtake a k
    have hb₂ : b.rdrop k ++ a.rtake k = b := hsuf ▸ List.rdrop_append_rtake b k
    have e₁ : L.syntacticClass a * L.syntacticClass b = L.syntacticClass b := by
      conv_lhs => rw [← ha₁, ← hb₁]
      rw [syntacticClass_append, syntacticClass_append, ← mul_assoc, hp, ← syntacticClass_append,
        hb₁]
    have e₂ : L.syntacticClass a * L.syntacticClass b = L.syntacticClass a := by
      conv_lhs => rw [← ha₂, ← hb₂]
      rw [syntacticClass_append, syntacticClass_append, mul_assoc,
        ← mul_assoc (L.syntacticClass (a.rtake k)), hq, ← syntacticClass_append, ha₂]
    exact e₂.symm.trans e₁
  · rw [List.take_of_length_le ha.le, List.take_of_length_le (by omega)] at hpre
    rw [hpre]

/-! ### Idempotent classes

An idempotent class of a nonempty word is also the class of arbitrarily long words, so it satisfies
the window condition of every window. -/

private theorem exists_le_length_syntacticClass_eq {u : List α} (hu : u ≠ [])
    (he : IsIdempotentElem (L.syntacticClass u)) (n : ℕ) :
    ∃ v : List α, n ≤ v.length ∧ L.syntacticClass v = L.syntacticClass u := by
  refine ⟨(List.replicate (n + 1) u).flatten, ?_, ?_⟩
  · simp only [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]
    exact n.le_succ.trans (Nat.le_mul_of_pos_right _ (List.length_pos_iff.2 hu))
  · rw [syntacticClass_flatten, List.map_replicate, List.prod_replicate, he.pow_succ_eq]

/-- In a definite language, an idempotent class of a nonempty word is a right zero. -/
theorem IsDefinite.isRightZero_syntacticClass_of_isIdempotentElem (h : L.IsDefinite k)
    {u : List α} (hu : u ≠ []) (he : IsIdempotentElem (L.syntacticClass u)) :
    IsRightZero (L.syntacticClass u) :=
  have ⟨_, hv, hvu⟩ := exists_le_length_syntacticClass_eq hu he k
  hvu ▸ h.isRightZero_syntacticClass hv

theorem IsReverseDefinite.isLeftZero_syntacticClass_of_isIdempotentElem
    (h : L.IsReverseDefinite k) {u : List α} (hu : u ≠ [])
    (he : IsIdempotentElem (L.syntacticClass u)) : IsLeftZero (L.syntacticClass u) :=
  have ⟨_, hv, hvu⟩ := exists_le_length_syntacticClass_eq hu he k
  hvu ▸ h.isLeftZero_syntacticClass hv

theorem IsGeneralizedDefinite.syntacticClass_mul_mul_self_of_isIdempotentElem
    (h : L.IsGeneralizedDefinite k) {u : List α} (hu : u ≠ [])
    (he : IsIdempotentElem (L.syntacticClass u)) (s : L.SyntacticMonoid) :
    L.syntacticClass u * s * L.syntacticClass u = L.syntacticClass u :=
  have ⟨_, hv, hvu⟩ := exists_le_length_syntacticClass_eq hu he k
  hvu ▸ h.syntacticClass_mul_mul_self hv s

/-! ### The syntactic semigroup -/

theorem isRightZero_iff_forall_syntacticSemigroupToMonoid_mul {x : L.SyntacticMonoid} :
    IsRightZero x ↔ ∀ s, L.syntacticSemigroupToMonoid s * x = x := by
  refine ⟨fun h s ↦ h _, fun h m ↦ ?_⟩
  rcases L.eq_one_or_mem_range_syntacticSemigroupToMonoid m with rfl | ⟨s, rfl⟩
  exacts [one_mul x, h s]

theorem isLeftZero_iff_forall_mul_syntacticSemigroupToMonoid {x : L.SyntacticMonoid} :
    IsLeftZero x ↔ ∀ s, x * L.syntacticSemigroupToMonoid s = x := by
  refine ⟨fun h s ↦ h _, fun h m ↦ ?_⟩
  rcases L.eq_one_or_mem_range_syntacticSemigroupToMonoid m with rfl | ⟨s, rfl⟩
  exacts [mul_one x, h s]

/-! #### From the language to the semigroup -/

theorem IsDefinite.isDefinite_syntacticSemigroup (h : L.IsDefinite k) :
    Semigroup.IsDefinite L.SyntacticSemigroup :=
  .of_isRightZero_map L.toSyntacticSemigroup_surjective fun w hw ↦ by
    obtain ⟨a, l⟩ := w
    refine .of_map ?_ L.syntacticSemigroupToMonoid_injective
    rw [syntacticSemigroupToMonoid_mk]
    exact h.isRightZero_syntacticClass hw

theorem IsReverseDefinite.isReverseDefinite_syntacticSemigroup (h : L.IsReverseDefinite k) :
    Semigroup.IsReverseDefinite L.SyntacticSemigroup :=
  .of_isLeftZero_map L.toSyntacticSemigroup_surjective fun w hw ↦ by
    obtain ⟨a, l⟩ := w
    refine .of_map ?_ L.syntacticSemigroupToMonoid_injective
    rw [syntacticSemigroupToMonoid_mk]
    exact h.isLeftZero_syntacticClass hw

theorem IsGeneralizedDefinite.isLocallyTrivial_syntacticSemigroup
    (h : L.IsGeneralizedDefinite k) : Semigroup.IsLocallyTrivial L.SyntacticSemigroup :=
  .of_map_mul_map_eq L.toSyntacticSemigroup_surjective fun w hw s ↦
    L.syntacticSemigroupToMonoid_injective <| by
      obtain ⟨a, l⟩ := w
      rw [map_mul, map_mul, syntacticSemigroupToMonoid_mk]
      exact h.syntacticClass_mul_mul_self hw _

/-! #### From the semigroup to the language -/

section Converse

variable [Finite L.SyntacticSemigroup]

private theorem isEmpty_of_natCard_le_length_nil
    (hu : Nat.card L.SyntacticSemigroup ≤ ([] : List α).length) : IsEmpty L.SyntacticSemigroup :=
  not_nonempty_iff.1 fun _ ↦ (Nat.card_pos (α := L.SyntacticSemigroup)).not_ge hu

/-- A language with a definite syntactic semigroup `S` is `|S|`-definite. -/
theorem isDefinite_natCard_of_isDefinite_syntacticSemigroup
    (h : Semigroup.IsDefinite L.SyntacticSemigroup) :
    L.IsDefinite (Nat.card L.SyntacticSemigroup) := by
  refine isDefinite_iff_forall_isRightZero_syntacticClass.2 fun u hu ↦ ?_
  rw [isRightZero_iff_forall_syntacticSemigroupToMonoid_mul]
  rcases u with _ | ⟨a, l⟩
  · exact (isEmpty_of_natCard_le_length_nil hu).elim
  · intro s
    rw [← syntacticSemigroupToMonoid_mk, ← map_mul, h.isRightZero_map _ (w := ⟨a, l⟩) hu s]

theorem isReverseDefinite_natCard_of_isReverseDefinite_syntacticSemigroup
    (h : Semigroup.IsReverseDefinite L.SyntacticSemigroup) :
    L.IsReverseDefinite (Nat.card L.SyntacticSemigroup) := by
  refine isReverseDefinite_iff_forall_isLeftZero_syntacticClass.2 fun u hu ↦ ?_
  rw [isLeftZero_iff_forall_mul_syntacticSemigroupToMonoid]
  rcases u with _ | ⟨a, l⟩
  · exact (isEmpty_of_natCard_le_length_nil hu).elim
  · intro s
    rw [← syntacticSemigroupToMonoid_mk, ← map_mul, h.isLeftZero_map _ (w := ⟨a, l⟩) hu s]

theorem isGeneralizedDefinite_natCard_of_isLocallyTrivial_syntacticSemigroup
    (h : Semigroup.IsLocallyTrivial L.SyntacticSemigroup) :
    L.IsGeneralizedDefinite (Nat.card L.SyntacticSemigroup) := by
  refine isGeneralizedDefinite_iff_forall_syntacticClass_mul_mul_self.2 fun u hu m ↦ ?_
  rcases u with _ | ⟨a, l⟩
  · rcases L.eq_one_or_mem_range_syntacticSemigroupToMonoid m with rfl | ⟨s, rfl⟩
    exacts [by simp, (isEmpty_of_natCard_le_length_nil hu).elim s]
  · replace hu : Nat.card _ ≤ (⟨a, l⟩ : FreeSemigroup α).length := hu
    rw [← syntacticSemigroupToMonoid_mk]
    rcases L.eq_one_or_mem_range_syntacticSemigroupToMonoid m with rfl | ⟨s, rfl⟩
    · rw [mul_one, ← map_mul, (h.isIdempotentElem_map _ hu).eq]
    · rw [← map_mul, ← map_mul, h.map_mul_map_eq _ hu]

theorem isDefinite_syntacticSemigroup_iff :
    Semigroup.IsDefinite L.SyntacticSemigroup ↔ ∃ k, L.IsDefinite k :=
  ⟨fun h ↦ ⟨_, isDefinite_natCard_of_isDefinite_syntacticSemigroup h⟩,
    fun ⟨_, h⟩ ↦ h.isDefinite_syntacticSemigroup⟩

theorem isReverseDefinite_syntacticSemigroup_iff :
    Semigroup.IsReverseDefinite L.SyntacticSemigroup ↔ ∃ k, L.IsReverseDefinite k :=
  ⟨fun h ↦ ⟨_, isReverseDefinite_natCard_of_isReverseDefinite_syntacticSemigroup h⟩,
    fun ⟨_, h⟩ ↦ h.isReverseDefinite_syntacticSemigroup⟩

theorem isLocallyTrivial_syntacticSemigroup_iff :
    Semigroup.IsLocallyTrivial L.SyntacticSemigroup ↔ ∃ k, L.IsGeneralizedDefinite k :=
  ⟨fun h ↦ ⟨_, isGeneralizedDefinite_natCard_of_isLocallyTrivial_syntacticSemigroup h⟩,
    fun ⟨_, h⟩ ↦ h.isLocallyTrivial_syntacticSemigroup⟩

/-- Over a finite alphabet, a language with a finite syntactic semigroup is finite or cofinite
exactly when its syntactic semigroup is both definite and reverse definite. -/
theorem isFiniteOrCofinite_iff_syntacticSemigroup [Finite α] :
    L.IsFiniteOrCofinite ↔ Semigroup.IsDefinite L.SyntacticSemigroup ∧
      Semigroup.IsReverseDefinite L.SyntacticSemigroup := by
  rw [isDefinite_syntacticSemigroup_iff, isReverseDefinite_syntacticSemigroup_iff,
    isFiniteOrCofinite_iff_exists_isDefinite_and_isReverseDefinite]

end Converse

/-! ### The Eilenberg correspondences -/

/-- The language variety of **D** consists of the definite languages. -/
theorem mem_languages_definiteVariety_iff [Finite α] :
    L ∈ Semigroup.definiteVariety.languages α ↔ ∃ k, L.IsDefinite k :=
  ⟨fun h ↦ have := h.1; isDefinite_syntacticSemigroup_iff.1 h.2,
    fun ⟨_, h⟩ ↦ ⟨h.isRegular.finite_syntacticSemigroup, h.isDefinite_syntacticSemigroup⟩⟩

/-- The language variety of **K** consists of the reverse definite languages. -/
theorem mem_languages_reverseDefiniteVariety_iff [Finite α] :
    L ∈ Semigroup.reverseDefiniteVariety.languages α ↔ ∃ k, L.IsReverseDefinite k :=
  ⟨fun h ↦ have := h.1; isReverseDefinite_syntacticSemigroup_iff.1 h.2,
    fun ⟨_, h⟩ ↦ ⟨h.isRegular.finite_syntacticSemigroup, h.isReverseDefinite_syntacticSemigroup⟩⟩

/-- The language variety of **LI** consists of the generalized definite languages. -/
theorem mem_languages_locallyTrivialVariety_iff [Finite α] :
    L ∈ Semigroup.locallyTrivialVariety.languages α ↔ ∃ k, L.IsGeneralizedDefinite k :=
  ⟨fun h ↦ have := h.1; isLocallyTrivial_syntacticSemigroup_iff.1 h.2,
    fun ⟨_, h⟩ ↦ ⟨h.isRegular.finite_syntacticSemigroup, h.isLocallyTrivial_syntacticSemigroup⟩⟩

end Language
