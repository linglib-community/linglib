module

public import Linglib.Semantics.Quantification.Defs
public import Mathlib.Order.UpperLower.Basic

/-!
# Properties of determiner denotations

This file proves the general properties of determiner denotations. The negations rotate the
monotonicities and preserve permutation invariance, and conservativity and the monotonicities
are closed under the Boolean operations and under adjectival restriction, as Keenan and Stavi
observe. Under conservativity, symmetry is
[intersectivity](##Quantifier.Det.Conservative.symm_iff_intersective) and the conjunction of ↑SW
and ↓NE monotonicity; a determiner denotation is restrictor monotone exactly when it is ↑SW and
↑SE monotone, and smoothness gives scope monotonicity, all as in Peters and Westerståhl. Van
Benthem's relational results characterize *all*, *some* and *no* by their relational properties
alone. Scope monotonicity is that every section of the determiner denotation is an upper set of
scopes. The sections of the conservative, quantity-invariant determiner denotations, which Peters
and Westerståhl call their freezings to a restrictor, are [exactly the
quantifiers](##Quantifier.exists_det_apply_eq_iff_livesOn) that live on a set and that the
permutations fixing it leave unchanged.

## References

* [keenan-stavi-1986]
* [peters-westerstahl-2006]
* [van-benthem-1984]
-/

@[expose] public section

namespace Quantifier

variable {α : Type*}

theorem individual_monotone (a : α) : Monotone (individual a) := fun _ _ h ha ↦ h ha

theorem individual_inter {a : α} {B B' : Set α} :
    individual a (B ∩ B') ↔ individual a B ∧ individual a B' :=
  Iff.rfl

section QuantityInvariant

variable {Q Q' : Quantifier α}

theorem QuantityInvariant.compl (h : Q.QuantityInvariant) : Qᶜ.QuantityInvariant :=
  fun σ B ↦ not_congr (h σ B)

theorem QuantityInvariant.inf (h : Q.QuantityInvariant) (h' : Q'.QuantityInvariant) :
    (Q ⊓ Q').QuantityInvariant :=
  fun σ B ↦ and_congr (h σ B) (h' σ B)

theorem QuantityInvariant.sup (h : Q.QuantityInvariant) (h' : Q'.QuantityInvariant) :
    (Q ⊔ Q').QuantityInvariant :=
  fun σ B ↦ or_congr (h σ B) (h' σ B)

end QuantityInvariant

namespace Det

variable {d d' : Det α} {A B : Set α}

/-! ### The negations -/

theorem ScopeMonotone.compl (h : d.ScopeMonotone) : dᶜ.ScopeAntitone :=
  fun A _ _ hB hn hd ↦ hn (h A hB hd)

theorem ScopeAntitone.compl (h : d.ScopeAntitone) : dᶜ.ScopeMonotone :=
  fun A _ _ hB hn hd ↦ hn (h A hB hd)

theorem ScopeMonotone.innerNeg (h : d.ScopeMonotone) : d.innerNeg.ScopeAntitone :=
  fun A _ _ hB ↦ h A (Set.compl_subset_compl.2 hB)

theorem ScopeAntitone.innerNeg (h : d.ScopeAntitone) : d.innerNeg.ScopeMonotone :=
  fun A _ _ hB ↦ h A (Set.compl_subset_compl.2 hB)

theorem RestrictorMonotone.compl (h : d.RestrictorMonotone) : dᶜ.RestrictorAntitone :=
  fun B _ _ hA hn hd ↦ hn (h B hA hd)

theorem RestrictorAntitone.compl (h : d.RestrictorAntitone) : dᶜ.RestrictorMonotone :=
  fun B _ _ hA hn hd ↦ hn (h B hA hd)

@[simp] theorem innerNeg_innerNeg (d : Det α) : d.innerNeg.innerNeg = d := by
  funext A B; simp [innerNeg]

@[simp] theorem dual_dual (d : Det α) : d.dual.dual = d := by
  funext A B; simp [dual, innerNeg]

theorem innerNeg_compl (d : Det α) : dᶜ.innerNeg = d.innerNegᶜ := rfl

/-- A determiner denotation is scope antitone exactly when its inner negation is scope
monotone. -/
theorem scopeAntitone_iff_innerNeg : d.ScopeAntitone ↔ d.innerNeg.ScopeMonotone :=
  ⟨ScopeAntitone.innerNeg, fun h ↦ by simpa using h.innerNeg⟩

/-- A determiner denotation is scope monotone exactly when each of its sections is an upper set of
scopes. -/
theorem scopeMonotone_iff_isUpperSet : d.ScopeMonotone ↔ ∀ A, IsUpperSet {B | d A B} :=
  forall_congr' fun _ ↦ isUpperSet_setOfPred.symm

theorem QuantityInvariant.compl (h : d.QuantityInvariant) : dᶜ.QuantityInvariant :=
  fun σ A B ↦ not_congr (h σ A B)

theorem QuantityInvariant.innerNeg (h : d.QuantityInvariant) : d.innerNeg.QuantityInvariant :=
  fun σ A B ↦ h σ A Bᶜ

theorem QuantityInvariant.dual (h : d.QuantityInvariant) : d.dual.QuantityInvariant :=
  h.innerNeg.compl

theorem QuantityInvariant.inf (h : d.QuantityInvariant) (h' : d'.QuantityInvariant) :
    (d ⊓ d').QuantityInvariant :=
  fun σ A B ↦ and_congr (h σ A B) (h' σ A B)

theorem QuantityInvariant.sup (h : d.QuantityInvariant) (h' : d'.QuantityInvariant) :
    (d ⊔ d').QuantityInvariant :=
  fun σ A B ↦ or_congr (h σ A B) (h' σ A B)

/-- The section of a quantity-invariant determiner denotation at the universe is quantity
invariant. -/
theorem QuantityInvariant.apply_univ (h : d.QuantityInvariant) : (d .univ).QuantityInvariant :=
  fun σ B ↦ by simpa using h σ .univ B

/-! ### Conservativity, symmetry and strength -/

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

/-! ### Left monotonicity and smoothness -/

theorem RestrictorMonotone.upSE (h : d.RestrictorMonotone) : d.UpSEMon :=
  fun _ B _ hA _ ↦ h B hA

theorem RestrictorMonotone.upSW (h : d.RestrictorMonotone) : d.UpSWMon :=
  fun _ B _ hA _ ↦ h B hA

theorem RestrictorAntitone.downNW (h : d.RestrictorAntitone) : d.DownNWMon :=
  fun _ B _ hA _ ↦ h B hA

theorem RestrictorAntitone.downNE (h : d.RestrictorAntitone) : d.DownNEMon :=
  fun _ B _ hA _ ↦ h B hA

/-- A determiner denotation is restrictor monotone exactly when it is ↑SW and ↑SE monotone. -/
theorem restrictorMonotone_iff_upSW_and_upSE :
    d.RestrictorMonotone ↔ d.UpSWMon ∧ d.UpSEMon := by
  refine ⟨fun h ↦ ⟨h.upSW, h.upSE⟩, fun ⟨hSW, hSE⟩ B A A' hA hd ↦ ?_⟩
  refine hSE (A ∪ A' \ B) B A' (Set.union_subset hA Set.sdiff_subset) Set.subset_union_right
    (hSW A B _ Set.subset_union_left ?_ hd)
  rintro x ⟨hx | hx, hB⟩
  exacts [hx, absurd hB hx.2]

/-- A determiner denotation is restrictor antitone exactly when it is ↓NW and ↓NE monotone. -/
theorem restrictorAntitone_iff_downNW_and_downNE :
    d.RestrictorAntitone ↔ d.DownNWMon ∧ d.DownNEMon := by
  refine ⟨fun h ↦ ⟨h.downNW, h.downNE⟩, fun ⟨hNW, hNE⟩ B A A' hA hd ↦ ?_⟩
  refine hNW (A ∪ A' ∩ B) B A Set.subset_union_left ?_
    (hNE A' B _ (Set.union_subset hA Set.inter_subset_left) Set.subset_union_right hd)
  rintro x ⟨hx | hx, hB⟩
  exacts [hx, absurd hx.2 hB]

theorem UpSEMon.compl (h : d.UpSEMon) : dᶜ.DownNWMon :=
  fun A B A' h₁ h₂ hn hd ↦ hn (h A' B A h₁ h₂ hd)

theorem DownNWMon.compl (h : d.DownNWMon) : dᶜ.UpSEMon :=
  fun A B A' h₁ h₂ hn hd ↦ hn (h A' B A h₁ h₂ hd)

theorem UpSWMon.compl (h : d.UpSWMon) : dᶜ.DownNEMon :=
  fun A B A' h₁ h₂ hn hd ↦ hn (h A' B A h₁ h₂ hd)

theorem DownNEMon.compl (h : d.DownNEMon) : dᶜ.UpSWMon :=
  fun A B A' h₁ h₂ hn hd ↦ hn (h A' B A h₁ h₂ hd)

theorem DownNEMon.innerNeg (h : d.DownNEMon) : d.innerNeg.DownNWMon :=
  fun A B A' h₁ h₂ ↦ h A Bᶜ A' h₁ h₂

theorem DownNWMon.innerNeg (h : d.DownNWMon) : d.innerNeg.DownNEMon :=
  fun A B A' h₁ h₂ ↦ h A Bᶜ A' h₁ (by rwa [Set.sdiff_compl])

theorem UpSEMon.innerNeg (h : d.UpSEMon) : d.innerNeg.UpSWMon :=
  fun A B A' h₁ h₂ ↦ h A Bᶜ A' h₁ (by rwa [Set.sdiff_compl])

theorem UpSWMon.innerNeg (h : d.UpSWMon) : d.innerNeg.UpSEMon :=
  fun A B A' h₁ h₂ ↦ h A Bᶜ A' h₁ h₂

theorem smooth_iff_coSmooth_compl : d.Smooth ↔ dᶜ.CoSmooth :=
  ⟨fun ⟨hNE, hSE⟩ ↦ ⟨hSE.compl, hNE.compl⟩,
    fun ⟨hNW, hSW⟩ ↦ ⟨by simpa using hSW.compl, by simpa using hNW.compl⟩⟩

theorem smooth_iff_coSmooth_innerNeg : d.Smooth ↔ d.innerNeg.CoSmooth :=
  ⟨fun ⟨hNE, hSE⟩ ↦ ⟨hNE.innerNeg, hSE.innerNeg⟩,
    fun ⟨hNW, hSW⟩ ↦ ⟨by simpa using hNW.innerNeg, by simpa using hSW.innerNeg⟩⟩

/-- A smooth conservative determiner denotation is scope monotone. -/
theorem Smooth.scopeMonotone (h : d.Smooth) (hC : d.Conservative) : d.ScopeMonotone := by
  intro A B B' hB hd
  have h₁ : d (A ∩ (B ∪ B'ᶜ)) B :=
    h.1 A B _ Set.inter_subset_left (fun x hx ↦ ⟨hx.1, .inl hx.2⟩) hd
  have h₂ : d (A ∩ (B ∪ B'ᶜ)) B' := (hC.iff_of_inter_eq <| Set.ext fun x ↦
    ⟨fun ⟨hx, h⟩ ↦ ⟨hx, hB h⟩, fun ⟨hx, h⟩ ↦ ⟨hx, hx.2.resolve_right fun hn ↦ hn h⟩⟩).1 h₁
  exact h.2 _ B' A Set.inter_subset_left (fun x hx ↦ ⟨hx.1, .inr hx.2⟩) h₂

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

/-! ### Boolean closure -/

theorem Conservative.compl (h : d.Conservative) : dᶜ.Conservative :=
  fun A B ↦ not_congr (h A B)

theorem Conservative.inf (h : d.Conservative) (h' : d'.Conservative) : (d ⊓ d').Conservative :=
  fun A B ↦ and_congr (h A B) (h' A B)

theorem Conservative.sup (h : d.Conservative) (h' : d'.Conservative) : (d ⊔ d').Conservative :=
  fun A B ↦ or_congr (h A B) (h' A B)

theorem ScopeMonotone.inf (h : d.ScopeMonotone) (h' : d'.ScopeMonotone) :
    (d ⊓ d').ScopeMonotone :=
  fun A _ _ hB hd ↦ ⟨h A hB hd.1, h' A hB hd.2⟩

theorem ScopeAntitone.inf (h : d.ScopeAntitone) (h' : d'.ScopeAntitone) :
    (d ⊓ d').ScopeAntitone :=
  fun A _ _ hB hd ↦ ⟨h A hB hd.1, h' A hB hd.2⟩

theorem ScopeMonotone.sup (h : d.ScopeMonotone) (h' : d'.ScopeMonotone) :
    (d ⊔ d').ScopeMonotone :=
  fun A _ _ hB hd ↦ hd.imp (h A hB) (h' A hB)

theorem ScopeAntitone.sup (h : d.ScopeAntitone) (h' : d'.ScopeAntitone) :
    (d ⊔ d').ScopeAntitone :=
  fun A _ _ hB hd ↦ hd.imp (h A hB) (h' A hB)

theorem Existential.conservative (h : d.Existential) : d.Conservative :=
  fun A B ↦ by rw [h A B, h A (A ∩ B), ← Set.inter_assoc, Set.inter_self]

theorem Existential.adjRestrict (h : d.Existential) (C : Set α) : (d.adjRestrict C).Existential :=
  fun A B ↦ by
    simp only [Det.adjRestrict]
    rw [h, Set.inter_right_comm]

theorem Conservative.adjRestrict (h : d.Conservative) (C : Set α) :
    (d.adjRestrict C).Conservative :=
  fun _ _ ↦ h.iff_of_inter_eq <| Set.ext fun _ ↦
    ⟨fun ⟨hx, hB⟩ ↦ ⟨hx, hx.1, hB⟩, fun ⟨hx, _, hB⟩ ↦ ⟨hx, hB⟩⟩

theorem ScopeMonotone.adjRestrict (h : d.ScopeMonotone) (C : Set α) :
    (d.adjRestrict C).ScopeMonotone :=
  fun A ↦ h (A ∩ C)

theorem ScopeAntitone.adjRestrict (h : d.ScopeAntitone) (C : Set α) :
    (d.adjRestrict C).ScopeAntitone :=
  fun A ↦ h (A ∩ C)

/-! ### Relational characterizations

[van-benthem-1984] reads a determiner denotation as a relation between sets and characterizes
*all*, *some* and *no* by their relational properties. -/

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

theorem ScopeMonotone.rightContinuous (h : d.ScopeMonotone) : d.RightContinuous :=
  fun A _ _ _ h₁ _ hd _ ↦ h A h₁ hd

theorem ScopeAntitone.rightContinuous (h : d.ScopeAntitone) : d.RightContinuous :=
  fun A _ _ _ _ h₂ _ hd ↦ h A h₂ hd

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

private theorem preimage_swap_singleton [DecidableEq α] (x a : α) :
    Equiv.swap x a ⁻¹' {a} = {x} := by
  ext y; simp [Equiv.swap_apply_eq_iff]

/-- *Some* is the only symmetric quasi-reflexive conservative determiner denotation that is
permutation invariant and holds of a singleton but not everywhere ([van-benthem-1984],
Theorem 3.3.2). -/
theorem Conservative.iff_inter_nonempty (h : d.Conservative) [Std.Symm d]
    (hQ : d.QuasiReflexive) (hI : d.QuantityInvariant) (hx : ∃ x, d {x} {x})
    (hA : ∃ A, ¬ d A A) : d A B ↔ (A ∩ B).Nonempty := by
  classical
  have up {C D : Set α} (hCD : C ⊆ D) (hC : d C C) : d D D :=
    hQ D C ((h.symm_iff_intersective.1 inferInstance D C C C
      (by rw [Set.inter_eq_right.2 hCD, Set.inter_self])).2 hC)
  rw [h.iff_inter_inter]
  refine ⟨fun hd ↦ Set.nonempty_iff_ne_empty.2 fun he ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · obtain ⟨A₀, hA₀⟩ := hA
    exact hA₀ (up (Set.empty_subset A₀) (he ▸ hd))
  · obtain ⟨x, hx⟩ := hx
    have hs : d {a} {a} := by
      rw [← hI (Equiv.swap x a) {a} {a}, preimage_swap_singleton]; exact hx
    exact up (Set.singleton_subset_iff.2 ha) hs

/-- *No* is the only symmetric quasi-universal conservative determiner denotation that is
permutation invariant and fails of a singleton but holds somewhere ([van-benthem-1984],
Corollary 3.3.3). -/
theorem Conservative.iff_disjoint (h : d.Conservative) [Std.Symm d]
    (hQ : d.QuasiUniversal) (hI : d.QuantityInvariant) (hx : ∃ x, ¬ d {x} {x})
    (hA : ∃ A, d A A) : d A B ↔ Disjoint A B := by
  classical
  have down {C D : Set α} (hCD : C ⊆ D) (hD : d D D) : d C C := by
    have := Std.Symm.symm _ _ (hQ D C hD)
    rwa [h, Set.inter_eq_left.2 hCD] at this
  rw [h.iff_inter_inter, Set.disjoint_iff_inter_eq_empty]
  refine ⟨fun hd ↦ Set.eq_empty_iff_forall_notMem.2 fun a ha ↦ ?_, fun he ↦ ?_⟩
  · obtain ⟨x, hx⟩ := hx
    have ha' : d {a} {a} := down (Set.singleton_subset_iff.2 ha) hd
    rw [← hI (Equiv.swap x a) {a} {a}, preimage_swap_singleton] at ha'
    exact hx ha'
  · obtain ⟨A₀, hA₀⟩ := hA
    exact he ▸ down (Set.empty_subset A₀) hA₀

end Det

open Set in
/-- The quantifiers `d A` that a conservative, quantity-invariant determiner denotation gives at a
restrictor, [peters-westerstahl-2006]'s freezings of it, are the quantifiers that live on a set and
that the permutations fixing that set leave unchanged. -/
theorem exists_det_apply_eq_iff_livesOn {Q : Quantifier α} :
    (∃ d : Det α, d.Conservative ∧ d.QuantityInvariant ∧ ∃ A, d A = Q) ↔
      ∃ A, Q.LivesOn A ∧ ∀ σ : Equiv.Perm α, σ ⁻¹' A = A → ∀ B, Q (σ ⁻¹' B) ↔ Q B := by
  refine ⟨fun ⟨d, hC, hQ, A, hdQ⟩ ↦ hdQ ▸ ⟨A, hC.livesOn A, fun σ hσ B ↦ by
    simpa [hσ] using hQ σ A B⟩, fun ⟨J, hJ, hinv⟩ ↦ ?_⟩
  -- `d A B` when a permutation carries `J` onto `A` and `Q` holds of the part of `A ∩ B` it
  -- carries there
  let d : Det α := fun A B ↦ ∃ τ : Equiv.Perm α, τ ⁻¹' A = J ∧ Q (τ ⁻¹' (A ∩ B))
  have key : ∀ (σ : Equiv.Perm α) A B, d A B → d (σ ⁻¹' A) (σ ⁻¹' B) := by
    rintro σ A B ⟨τ, hτ, hB⟩
    refine ⟨τ.trans σ.symm, ?_, ?_⟩
    · rw [← hτ]; ext x; simp
    · have : ⇑(τ.trans σ.symm) ⁻¹' (σ ⁻¹' A ∩ σ ⁻¹' B) = τ ⁻¹' (A ∩ B) := by ext x; simp
      rwa [this]
  have e : ∀ (σ : Equiv.Perm α) X, ⇑σ.symm ⁻¹' (σ ⁻¹' X) = X := fun σ X ↦ by ext; simp
  refine ⟨d, fun A B ↦ ?_, fun σ A B ↦ ⟨fun h ↦ ?_, key σ A B⟩, J, funext fun B ↦ propext ?_⟩
  · simp only [d, ← inter_assoc, inter_self]
  · simpa only [e] using key σ.symm _ _ h
  · exact ⟨fun ⟨τ, hτ, hB⟩ ↦ (hJ B).2 ((hinv τ hτ _).1 hB),
      fun hB ↦ ⟨Equiv.refl α, rfl, (hJ B).1 hB⟩⟩

end Quantifier
