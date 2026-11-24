module

public import Linglib.Semantics.Quantifier.Monotone

/-!
# Conservative determiner denotations

A determiner denotation is conservative when `d A B ↔ d A (A ∩ B)`: only the part of the scope
inside the restrictor matters. It is intersective when `d A B` depends on `A ∩ B` alone, and
co-intersective when it depends on `A \ B` alone; both imply conservativity.

This file proves the facts about these properties and their interaction with monotonicity.
Conservativity is closed under the Boolean operations and under adjectival restriction. For a
conservative determiner denotation, being symmetric is the same as being intersective, and the
same as being both ↑SW and ↓NE monotone. Van Benthem's relational results characterize *all*
among the conservative determiner denotations by its properties as a relation between sets; his
characterizations of *some* and *no* use permutation invariance and are in
`Quantifier/Invariance.lean`.

## Main results

* `Quantifier.Det.Conservative.symm_iff_intersective`: a conservative determiner denotation is
  symmetric if and only if it is intersective.
* `Quantifier.Det.Smooth.scopeMonotone`: a smooth conservative determiner denotation is scope
  monotone.
* `Quantifier.Det.Conservative.iff_subset`: inclusion is the only reflexive antisymmetric
  conservative determiner denotation.
* `Quantifier.Det.satisfiesUniversals_iff`: Barwise and Cooper's determiner universal and
  monotonicity constraint hold if and only if the determiner denotation is conservative and
  right continuous.

## References

* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [peters-westerstahl-2006]
* [van-benthem-1984]
-/

public section

namespace Quantifier

variable {α : Type*}

namespace Det

variable {d d' : Det α} {A B : Set α}

theorem conservative_iff_livesOn : d.Conservative ↔ ∀ A, (d A).LivesOn A := .rfl

theorem Conservative.iff_of_inter_eq (h : d.Conservative) {B' : Set α} (hB : A ∩ B = A ∩ B') :
    d A B ↔ d A B' := by
  rw [h A B, h A B', hB]

/-- A conservative determiner denotation does not distinguish scopes that agree on the
restrictor. -/
theorem Conservative.congr_scope (h : d.Conservative) {B' : Set α}
    (hB : ∀ x ∈ A, x ∈ B ↔ x ∈ B') : d A B ↔ d A B' :=
  h.iff_of_inter_eq <| Set.ext fun x ↦ and_congr_right (hB x)

/-- An intersective determiner denotation is symmetric. -/
theorem Intersective.symm (h : d.Intersective) : Std.Symm d :=
  ⟨fun A B ↦ (h A B B A (Set.inter_comm A B)).1⟩

theorem Conservative.iff_inter_inter (h : d.Conservative) [Std.Symm d] :
    d A B ↔ d (A ∩ B) (A ∩ B) :=
  calc d A B ↔ d A (A ∩ B) := h A B
    _ ↔ d (A ∩ B) A := ⟨Std.Symm.symm _ _, Std.Symm.symm _ _⟩
    _ ↔ d (A ∩ B) (A ∩ B ∩ A) := h _ _
    _ ↔ d (A ∩ B) (A ∩ B) := by rw [Set.inter_eq_left.2 Set.inter_subset_left]

/-- Under conservativity a determiner denotation is symmetric exactly when it is intersective,
which is why the symmetric determiners are the ones that occur in *there*-sentences. -/
theorem Conservative.symm_iff_intersective (h : d.Conservative) : Std.Symm d ↔ d.Intersective :=
  ⟨fun _ A B A' B' hAB ↦ by rw [h.iff_inter_inter, h.iff_inter_inter (A := A'), hAB],
    Intersective.symm⟩

/-- A conservative symmetric determiner denotation that fails somewhere is not positive
strong. -/
theorem Conservative.not_positiveStrong (h : d.Conservative) [Std.Symm d]
    (hd : ∃ A B, ¬ d A B) : ¬ d.PositiveStrong := fun hs ↦
  let ⟨_, _, hn⟩ := hd
  hn (h.iff_inter_inter.2 (hs _))

/-- A smooth conservative determiner denotation is scope monotone. -/
theorem Smooth.scopeMonotone (h : d.Smooth) (hC : d.Conservative) : d.ScopeMonotone := by
  intro A B B' hB hd
  have h₁ : d (A ∩ (B ∪ B'ᶜ)) B :=
    h.1 A B _ Set.inter_subset_left (fun x hx ↦ ⟨hx.1, .inl hx.2⟩) hd
  have h₂ : d (A ∩ (B ∪ B'ᶜ)) B' := (hC.iff_of_inter_eq <| Set.ext fun x ↦
    ⟨fun ⟨hx, h⟩ ↦ ⟨hx, hB h⟩, fun ⟨hx, h⟩ ↦ ⟨hx, hx.2.resolve_right fun hn ↦ hn h⟩⟩).1 h₁
  exact h.2 (A ∩ (B ∪ B'ᶜ)) B' A Set.inter_subset_left (fun x hx ↦ ⟨hx.1, .inr hx.2⟩) h₂

theorem Intersective.upSWMon (h : d.Intersective) : d.UpSWMon :=
  fun A B _ h₁ h₂ ↦ (h A B _ B (Set.Subset.antisymm
    (fun _ hx ↦ ⟨h₁ hx.1, hx.2⟩) (fun _ hx ↦ ⟨h₂ hx, hx.2⟩))).1

theorem Intersective.downNEMon (h : d.Intersective) : d.DownNEMon :=
  fun A B _ h₁ h₂ ↦ (h A B _ B (Set.Subset.antisymm
    (fun _ hx ↦ ⟨h₂ hx, hx.2⟩) (fun _ hx ↦ ⟨h₁ hx.1, hx.2⟩))).1

/-- Under conservativity a determiner denotation is symmetric exactly when it is ↑SW and ↓NE
monotone. -/
theorem Conservative.symm_iff_upSW_and_downNE (h : d.Conservative) :
    Std.Symm d ↔ d.UpSWMon ∧ d.DownNEMon := by
  refine ⟨fun hS ↦ ⟨(h.symm_iff_intersective.1 hS).upSWMon,
    (h.symm_iff_intersective.1 hS).downNEMon⟩, fun ⟨hSW, hNE⟩ ↦ ⟨fun A B hd ↦ ?_⟩⟩
  have h₁ : d (A ∪ B) (A ∩ B) :=
    hSW A _ _ Set.subset_union_left (fun _ hx ↦ hx.2.1) ((h A B).1 hd)
  have h₂ : d B (A ∩ B) := hNE _ _ B Set.subset_union_right (fun _ hx ↦ hx.2.2) h₁
  rwa [h B A, Set.inter_comm]

theorem Conservative.compl (h : d.Conservative) : dᶜ.Conservative :=
  fun A B ↦ not_congr (h A B)

theorem Conservative.inf (h : d.Conservative) (h' : d'.Conservative) : (d ⊓ d').Conservative :=
  fun A B ↦ and_congr (h A B) (h' A B)

theorem Conservative.sup (h : d.Conservative) (h' : d'.Conservative) : (d ⊔ d').Conservative :=
  fun A B ↦ or_congr (h A B) (h' A B)

theorem Intersective.iff_inter_univ (h : d.Intersective) : d A B ↔ d (A ∩ B) Set.univ :=
  h A B _ _ (Set.inter_univ _).symm

theorem intersective_iff : d.Intersective ↔ ∀ A B, d A B ↔ d (A ∩ B) Set.univ :=
  ⟨fun h _ _ ↦ h.iff_inter_univ, fun h A B A' B' e ↦ by rw [h A B, h A' B', e]⟩

/-- An intersective determiner denotation is unchanged by removing from its restrictor a set
disjoint from what the restrictor and the scope share. -/
theorem Intersective.sdiff_iff (h : d.Intersective) {C : Set α} (hC : Disjoint (A ∩ B) C) :
    d (A \ C) B ↔ d A B :=
  h _ _ _ _ (by rw [← Set.inter_sdiff_right_comm, hC.sdiff_eq_left])

/-- A co-intersective determiner denotation is unchanged by removing from its restrictor a set
disjoint from the part of the restrictor outside the scope. -/
theorem CoIntersective.sdiff_iff (h : d.CoIntersective) {C : Set α} (hC : Disjoint (A \ B) C) :
    d (A \ C) B ↔ d A B :=
  h _ _ _ _ (by rw [sdiff_right_comm, hC.sdiff_eq_left])

/-- A determiner denotation is co-intersective exactly when `d A B ↔ d univ (A → B)`, so that it
reduces to its value on the universe at the Boolean conditional. -/
theorem coIntersective_iff : d.CoIntersective ↔ ∀ A B, d A B ↔ d Set.univ (Aᶜ ∪ B) := by
  have e (A B : Set α) : Set.univ \ (Aᶜ ∪ B) = A \ B := by ext; simp
  exact ⟨fun h A B ↦ h A B _ _ (e A B).symm,
    fun h A B A' B' h' ↦ by
      rw [h A B, h A' B', show Aᶜ ∪ B = A'ᶜ ∪ B' by
        rw [← compl_compl (Aᶜ ∪ B), ← compl_compl (A'ᶜ ∪ B')]
        congr 1
        simpa [Set.compl_union, Set.sdiff_eq] using h']⟩

theorem Intersective.conservative (h : d.Intersective) : d.Conservative :=
  fun A B ↦ h A B _ _ (by rw [← Set.inter_assoc, Set.inter_self])

theorem CoIntersective.conservative (h : d.CoIntersective) : d.Conservative :=
  fun A B ↦ h A B _ _ (by simp)

/-- Under conservativity the intersection condition is intersectivity: the functions conservative
on both arguments are the intersective ones. -/
theorem Conservative.intersectionCondition_iff (h : d.Conservative) :
    d.IntersectionCondition ↔ d.Intersective := by
  refine ⟨fun h' A B A' B' e ↦ ?_, fun h' A B ↦
    h' _ _ _ _ (by rw [Set.inter_assoc, Set.inter_self])⟩
  have key (A B : Set α) : d A B ↔ d (A ∩ B) (A ∩ B) := by
    rw [h A B, h' A (A ∩ B), ← Set.inter_assoc, Set.inter_self]
  rw [key A B, key A' B', e]

theorem Intersective.adjRestrict (h : d.Intersective) (C : Set α) :
    (d.adjRestrict C).Intersective :=
  fun A B A' B' e ↦ h _ _ _ _ (by rw [Set.inter_right_comm, e, Set.inter_right_comm])

theorem Conservative.adjRestrict (h : d.Conservative) (C : Set α) :
    (d.adjRestrict C).Conservative :=
  fun _ _ ↦ h.iff_of_inter_eq <| Set.ext fun _ ↦
    ⟨fun ⟨hx, hB⟩ ↦ ⟨hx, hx.1, hB⟩, fun ⟨hx, _, hB⟩ ↦ ⟨hx, hB⟩⟩

/-- Inclusion is the only reflexive antisymmetric conservative determiner denotation
([van-benthem-1984], Theorem 3.1.1). -/
theorem Conservative.iff_subset (h : d.Conservative) (hR : d.PositiveStrong)
    [Std.Antisymm d] : d A B ↔ A ⊆ B := by
  refine ⟨fun hd ↦ ?_, fun hAB ↦ ?_⟩
  · have h₂ : d (A ∩ B) A := by
      rw [h, Set.inter_eq_left.2 Set.inter_subset_left]; exact hR _
    exact Set.inter_eq_left.1 (Std.Antisymm.antisymm _ _ ((h A B).1 hd) h₂).symm
  · rw [h, Set.inter_eq_left.2 hAB]; exact hR A

/-- A reflexive transitive conservative determiner denotation is scope monotone, Zwarts's
theorem ([van-benthem-1984], Theorem 4.1.1). -/
theorem Conservative.scopeMonotone_of_trans (h : d.Conservative) (hR : d.PositiveStrong)
    [IsTrans _ d] : d.ScopeMonotone :=
  fun A B _ hB hd ↦ IsTrans.trans A B _ hd (by rw [h, Set.inter_eq_left.2 hB]; exact hR B)

/-- A reflexive transitive conservative determiner denotation is restrictor antitone,
Zwarts's theorem ([van-benthem-1984], Theorem 4.1.1). -/
theorem Conservative.restrictorAntitone_of_trans (h : d.Conservative) (hR : d.PositiveStrong)
    [IsTrans _ d] : d.RestrictorAntitone :=
  fun _ A _ hA hd ↦ IsTrans.trans A _ _ (by rw [h, Set.inter_eq_left.2 hA]; exact hR A) hd

theorem ScopeMonotone.quasiReflexive (h : d.ScopeMonotone) (hC : d.Conservative) :
    d.QuasiReflexive :=
  fun A B hd ↦ h A Set.inter_subset_left ((hC A B).1 hd)

theorem ScopeAntitone.quasiUniversal (h : d.ScopeAntitone) (hC : d.Conservative) :
    d.QuasiUniversal :=
  fun A B hd ↦ (hC A B).2 (h A Set.inter_subset_left hd)

/-- Barwise and Cooper's monotonicity constraint is right continuity: a quantifier is a
conjunction of monotone quantifiers exactly when it holds at every scope between two at which it
holds, Thijsse's observation reported by [van-benthem-1984]. -/
theorem satisfiesUniversals_iff : d.SatisfiesUniversals ↔ d.Conservative ∧ d.RightContinuous :=
  ⟨fun h ↦ ⟨h.conservative, fun A ↦ ordConnected_setOf_iff_exists_eq_inf.2 (h.exists_eq_inf A)⟩,
    fun h ↦ ⟨h.1, fun A ↦ ordConnected_setOf_iff_exists_eq_inf.1 (h.2 A)⟩⟩

/-- An irreflexive almost-connected conservative determiner denotation is scope antitone
([van-benthem-1984], Theorem 4.1.2). -/
theorem Conservative.scopeAntitone_of_almostConnected (h : d.Conservative)
    (hI : d.NegativeStrong) (hA : d.AlmostConnected) : d.ScopeAntitone := by
  have : IsTrans _ dᶜ := ⟨fun A B C h₁ h₂ h₃ ↦ (hA A C B h₃).elim h₁ h₂⟩
  simpa using (h.compl.scopeMonotone_of_trans hI).compl

/-- An irreflexive almost-connected conservative determiner denotation is restrictor monotone
([van-benthem-1984], Theorem 4.1.2). -/
theorem Conservative.restrictorMonotone_of_almostConnected (h : d.Conservative)
    (hI : d.NegativeStrong) (hA : d.AlmostConnected) : d.RestrictorMonotone := by
  have : IsTrans _ dᶜ := ⟨fun A B C h₁ h₂ h₃ ↦ (hA A C B h₃).elim h₁ h₂⟩
  simpa using (h.compl.restrictorAntitone_of_trans hI).compl

theorem negativeStrong_of_asymm [Std.Asymm d] : d.NegativeStrong :=
  fun A hd ↦ Std.Asymm.asymm A A hd hd

theorem Circular.quasiReflexive (h : d.Circular) [Std.Symm d] : d.QuasiReflexive :=
  fun A B hd ↦ h A B A hd (Std.Symm.symm A B hd)

theorem Circular.symm (h : d.Circular) (hR : d.PositiveStrong) : Std.Symm d :=
  ⟨fun A B hd ↦ h A A B (hR A) hd⟩

end Det

end Quantifier
