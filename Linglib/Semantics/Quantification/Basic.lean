module

public import Linglib.Semantics.Quantification.Defs
public import Linglib.Semantics.Quantification.Properties
public import Linglib.Logic.Aristotelian.Square
public import Linglib.Semantics.Reference.Iota
public import Mathlib.Order.CompleteLattice.Basic

/-!
# The determiners *every*, *some*, *no* and *the*

This file defines the determiner denotations *every* (`A ⊆ B`), *some* (`A ∩ B` nonempty), *no*
(`A ⊆ Bᶜ`) and the Russellian *the*, whose truth conditions need no counting, and proves their
conservativity, monotonicity, symmetry, duality and square-of-opposition properties. The
properties checked are Barwise and Cooper's determiner universal and monotonicity constraint, Keenan and Stavi's Boolean
structure, and Peters and Westerståhl's left monotonicity and smoothness. The counting
quantifiers such as *most* and *few* are in `Quantification/Counting.lean`.

## Main definitions

* `every`, `Det.some`, `no`, `the`: the propositional denotations.
* `SatisfiesUniversals`: conservativity together with Barwise and Cooper's monotonicity
  constraint, which is right continuity in the scope (`satisfiesUniversals_iff`).
* `square`: the square of opposition of `every`, `no`, `some` and `not every` at a restrictor.

## Main results

* `every_eq_sInf_image`, `some_eq_sSup_image`, `no_eq_compl_sSup_image`: the three determiners
  are the infimum, the supremum and the complement of the supremum of the scope over the
  restrictor.
* `no_iff_disjoint`, `no_iff_not_some`: *no* is disjointness, the complement of *some*.
* `every_univ_iff`, `some_univ_iff`, `no_univ_iff`: with the whole universe as restrictor, the
  three hold of the universe, of the nonempty sets and of the empty set.
* `square_relations`: with a non-empty restrictor the four stand in all six relations of the
  square, so its cells (`Aristotelian.Square.cell`) divide the scopes into those covering all of
  the restrictor, some but not all of it, and none of it.

## References

* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [peters-westerstahl-2006]
* [russell-1905]
* [van-benthem-1984]
-/

@[expose] public section

namespace Quantifier.Det

variable {α : Type*} {A B : Set α}

/-! ### Denotations -/

/-- *Every* holds when the restrictor is included in the scope. -/
def every : Det α := fun A B ↦ A ⊆ B

/-- *Some* holds when the restrictor meets the scope. -/
protected def some : Det α := fun A B ↦ (A ∩ B).Nonempty

/-- *No* holds when the restrictor is included in the complement of the scope; it is the inner
negation of *every*. -/
def no : Det α := fun A B ↦ A ⊆ Bᶜ

/-- The singular definite of [russell-1905], `λA λB. ∃x. ∀y. (A(y) ↔ y = x) ∧ B(x)`. -/
def the : Det α := fun A B ↦ ∃ x, (∀ y, y ∈ A ↔ y = x) ∧ x ∈ B

theorem the_iff : the A B ↔ (∃! x, x ∈ A) ∧ A ⊆ B := by
  constructor
  · rintro ⟨x, hx, hB⟩
    exact ⟨⟨x, (hx x).2 rfl, fun y hy ↦ (hx y).1 hy⟩, fun y hy ↦ (hx y).1 hy ▸ hB⟩
  · rintro ⟨⟨x, hx, huniq⟩, hB⟩
    exact ⟨x, fun y ↦ ⟨huniq y, fun h ↦ h ▸ hx⟩, hB hx⟩

theorem the_iff_exists_mem_iota : the A B ↔ ∃ x ∈ iota (· ∈ A), x ∈ B :=
  exists_congr fun x ↦ and_congr_left' <|
    (funext_iff.trans <| forall_congr' fun _ ↦ eq_iff_iff.trans Iff.comm).symm.trans
      (iota_isPartialInv x (· ∈ A)).symm

theorem every_iff_le : every A B ↔ A ≤ B := .rfl

theorem no_iff_le_compl : no A B ↔ A ≤ Bᶜ := .rfl

theorem no_iff_disjoint : no A B ↔ Disjoint A B := Set.subset_compl_iff_disjoint_right

theorem no_iff_not_some : no A B ↔ ¬ Det.some A B :=
  no_iff_disjoint.trans <| Set.disjoint_iff_inter_eq_empty.trans Set.not_nonempty_iff_eq_empty.symm

@[simp] theorem every_univ_iff : every Set.univ B ↔ B = Set.univ := Set.univ_subset_iff

@[simp] theorem some_univ_iff : Det.some Set.univ B ↔ B.Nonempty := by simp [Det.some]

@[simp] theorem no_univ_iff : no Set.univ B ↔ B = ∅ := by simp [no, Set.univ_subset_iff]

/-- *Some* turns a union of restrictors into a join. -/
theorem some_union (A A' : Set α) : Det.some (A ∪ A') = Det.some A ⊔ Det.some A' := by
  funext B; simp [Det.some, Set.union_inter_distrib_right, Set.union_nonempty]

/-- *Every* turns a union of restrictors into a meet. -/
theorem every_union (A A' : Set α) : every (A ∪ A') = every A ⊓ every A' := by
  funext B; simp [every, Set.union_subset_iff]

/-- The Montague lift of `a` is *every* on `{a}`. -/
theorem _root_.Quantifier.individual_eq_every (a : α) : individual a = every {a} := by
  funext B; simp [individual, every]

section Decidable

variable [Fintype α] [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]

instance : Decidable (every A B) := inferInstanceAs (Decidable (∀ _, _))

instance : Decidable (Det.some A B) := inferInstanceAs (Decidable (∃ _, _ ∧ _))

instance : Decidable (no A B) := inferInstanceAs (Decidable (∀ _, _))

end Decidable

/-- A determiner denotation satisfies Barwise and Cooper's determiner universal and monotonicity
constraint (U3 and U6 of [barwise-cooper-1981]) when it is conservative, so that each `d A` lives
on `A`, and each of its noun phrases `d A` is a monotone quantifier or a conjunction of monotone
quantifiers. A monotone `d A` is its own conjunction with the trivial quantifier `⊤`. -/
def SatisfiesUniversals (d : Det α) : Prop :=
  d.Conservative ∧ ∀ A, ∃ Q₁ Q₂ : Quantifier α, (Monotone Q₁ ∨ Antitone Q₁) ∧
    (Monotone Q₂ ∨ Antitone Q₂) ∧ d A = Q₁ ⊓ Q₂

/-! ### Infima and suprema

At a restrictor `A`, `every A B` is the infimum of the truth values of `x ∈ B` for `x ∈ A`,
`Det.some A B` their supremum, and `no A B` the complement of their supremum, so the three
determiners are conjunction, disjunction and negative coordination over the restrictor. -/

theorem every_eq_sInf_image (A B : Set α) : every A B = sInf ((· ∈ B) '' A) := by
  rw [sInf_Prop_eq, Set.forall_mem_image]; rfl

theorem some_eq_sSup_image (A B : Set α) : Det.some A B = sSup ((· ∈ B) '' A) := by
  rw [sSup_Prop_eq, Set.exists_mem_image]; rfl

theorem no_eq_compl_sSup_image (A B : Set α) : no A B = (sSup ((· ∈ B) '' A))ᶜ := by
  rw [← some_eq_sSup_image]; exact propext no_iff_not_some

/-! ### Conservativity and permutation invariance -/

theorem conservative_every : (every : Det α).Conservative :=
  fun _ _ ↦ (Set.subset_inter_iff.trans (and_iff_right subset_rfl)).symm

theorem conservative_some : (Det.some : Det α).Conservative := fun A B ↦ by
  show (A ∩ B).Nonempty ↔ (A ∩ (A ∩ B)).Nonempty
  rw [← Set.inter_assoc, Set.inter_self]

theorem conservative_no : (no : Det α).Conservative := fun A B ↦
  no_iff_not_some.trans <| (not_congr (conservative_some A B)).trans no_iff_not_some.symm

theorem quantityInvariant_every : (every : Det α).QuantityInvariant :=
  fun σ _ _ ↦ σ.surjective.preimage_subset_preimage_iff

theorem quantityInvariant_some : (Det.some : Det α).QuantityInvariant :=
  fun σ A B ↦ σ.surjective.nonempty_preimage (s := A ∩ B)

theorem quantityInvariant_no : (no : Det α).QuantityInvariant := quantityInvariant_every.innerNeg

/-! ### Scope monotonicity -/

theorem scopeMonotone_every : (every : Det α).ScopeMonotone := fun _ _ _ h h' ↦ h'.trans h

theorem scopeMonotone_some : (Det.some : Det α).ScopeMonotone :=
  fun A _ _ h h' ↦ h'.mono (Set.inter_subset_inter_right A h)

theorem scopeAntitone_no : (no : Det α).ScopeAntitone :=
  fun _ _ _ h h' ↦ h'.trans (Set.compl_subset_compl.2 h)

theorem scopeMonotone_the : (the : Det α).ScopeMonotone :=
  fun _ _ _ h ⟨x, hA, hB⟩ ↦ ⟨x, hA, h hB⟩

theorem not_scopeAntitone_some [Nonempty α] : ¬ (Det.some : Det α).ScopeAntitone := fun h ↦
  let ⟨x⟩ := ‹Nonempty α›
  (h Set.univ (Set.empty_subset _) ⟨x, Set.mem_univ x, Set.mem_univ x⟩).ne_empty (Set.inter_empty _)

theorem not_scopeAntitone_every [Nonempty α] : ¬ (every : Det α).ScopeAntitone := fun h ↦
  let ⟨x⟩ := ‹Nonempty α›
  Set.notMem_empty x (h Set.univ (Set.empty_subset _) subset_rfl (Set.mem_univ x))

theorem monotone_every (A : Set α) : Monotone (every A) := scopeMonotone_every A

theorem monotone_some (A : Set α) : Monotone (Det.some A) := scopeMonotone_some A

theorem antitone_no (A : Set α) : Antitone (no A) := scopeAntitone_no A

/-! ### Symmetry and intersectivity -/

instance symm_some : Std.Symm (Det.some : Det α) :=
  ⟨fun A B h ↦ by rwa [Det.some, Set.inter_comm]⟩

instance symm_no : Std.Symm (no : Det α) := ⟨fun _ _ h ↦ Set.subset_compl_comm.1 h⟩

theorem intersective_some : (Det.some : Det α).Intersective :=
  fun _ _ _ _ h ↦ by rw [Det.some, Det.some, h]

theorem intersective_no : (no : Det α).Intersective := fun A B A' B' h ↦
  no_iff_not_some.trans <| (not_congr (intersective_some A B A' B' h)).trans no_iff_not_some.symm

/-! ### Anti-additivity -/

theorem leftAntiAdditive_every : (every : Det α).LeftAntiAdditive :=
  fun _ _ _ ↦ propext Set.union_subset_iff

theorem leftAntiAdditive_no : (no : Det α).LeftAntiAdditive :=
  fun _ _ _ ↦ propext Set.union_subset_iff

theorem rightAntiAdditive_no : (no : Det α).RightAntiAdditive := fun A ↦
  isAntiAdditive_iff.2 fun B B' ↦ by rw [no, Set.compl_union, Set.subset_inter_iff]; rfl

/-! ### Duality -/

theorem innerNeg_every : (every : Det α).innerNeg = no := rfl

theorem compl_some : (Det.some : Det α)ᶜ = no := by
  funext A B; exact propext no_iff_not_some.symm

theorem dual_every : (every : Det α).dual = Det.some := by
  rw [dual, innerNeg_every, ← compl_some, compl_compl]

/-! ### Strength and existentiality -/

theorem positiveStrong_every : (every : Det α).PositiveStrong := fun _ ↦ subset_rfl

theorem not_no_self (hA : A.Nonempty) : ¬ no A A := fun h ↦
  let ⟨_, hx⟩ := hA
  h hx hx

theorem existential_some : (Det.some : Det α).Existential := fun A B ↦ by
  rw [Det.some, Det.some, Set.inter_univ]

theorem existential_no : (no : Det α).Existential := fun A B ↦
  no_iff_not_some.trans <| (not_congr (existential_some A B)).trans no_iff_not_some.symm

/-! ### Relational properties ([van-benthem-1984]) -/

instance isTrans_every : IsTrans _ (every : Det α) := ⟨fun _ _ _ h₁ h₂ ↦ h₁.trans h₂⟩

instance antisymm_every : Std.Antisymm (every : Det α) := ⟨fun _ _ ↦ Set.Subset.antisymm⟩

theorem quasiReflexive_some : (Det.some : Det α).QuasiReflexive :=
  fun _ _ ⟨x, hx⟩ ↦ ⟨x, hx.1, hx.1⟩

theorem quasiUniversal_no : (no : Det α).QuasiUniversal := fun _ _ h _ hx ↦ absurd hx (h hx)

/-! ### Double monotonicity ([van-benthem-1984]) -/

theorem restrictorAntitone_every : (every : Det α).RestrictorAntitone :=
  fun _ _ _ hA h ↦ hA.trans h

theorem restrictorMonotone_some : (Det.some : Det α).RestrictorMonotone :=
  fun B _ _ hA h ↦ h.mono (Set.inter_subset_inter_left B hA)

theorem restrictorAntitone_no : (no : Det α).RestrictorAntitone := fun _ _ _ hA h ↦ hA.trans h

theorem doubleMono_every :
    (every : Det α).RestrictorAntitone ∧ (every : Det α).ScopeMonotone :=
  ⟨restrictorAntitone_every, scopeMonotone_every⟩

theorem doubleMono_some :
    (Det.some : Det α).RestrictorMonotone ∧ (Det.some : Det α).ScopeMonotone :=
  ⟨restrictorMonotone_some, scopeMonotone_some⟩

theorem doubleMono_no : (no : Det α).RestrictorAntitone ∧ (no : Det α).ScopeAntitone :=
  ⟨restrictorAntitone_no, scopeAntitone_no⟩

theorem doubleMono_compl_every :
    (every : Det α)ᶜ.RestrictorMonotone ∧ (every : Det α)ᶜ.ScopeAntitone :=
  ⟨restrictorAntitone_every.compl, scopeMonotone_every.compl⟩

theorem scopeIntersective_every : (every : Det α).ScopeIntersective :=
  fun _ _ _ ↦ Set.subset_inter

theorem filtrating_every : (every : Det α).Filtrating :=
  ⟨scopeMonotone_every, scopeIntersective_every⟩

/-! ### Aristotelian square of opposition

At a restrictor `A`, the denotations `every A`, `no A`, `Det.some A` and `everyᶜ A` are the corners
of a square in the Boolean algebra `Quantifier α`. Outer negation is the Boolean complement, so the
diagonals are contradictory at every restrictor. Contrariety, and with it the subalternations
and subcontrariety, needs existential import: at an empty restrictor `every` and `no` both hold
vacuously (`a_e_contrary`), and `square_relations` assumes a nonempty one. -/

/-- At a restrictor `A` the four determiners form a square of opposition. -/
def square (A : Set α) : Aristotelian.Square (Quantifier α) where
  A := every A
  E := no A
  I := Det.some A
  O := (every : Det α)ᶜ A

theorem every_contradicts_notEvery (A B : Set α) :
    (every : Det α) A B ↔ ¬ ((every : Det α)ᶜ A B) := by
  simp [compl_apply, Classical.not_not]

theorem a_e_contrary : every A B → no A B → A = ∅ :=
  fun hA hE ↦ Set.eq_empty_of_forall_notMem fun _ hx ↦ hE hx (hA hx)

/-- With a nonempty restrictor the four determiners stand in all six relations of the square. -/
theorem square_relations (hA : A.Nonempty) : Aristotelian.SquareRelations (square A) :=
  .of_disjoint (funext fun _ ↦ propext <| iff_not_comm.mp no_iff_not_some) rfl <|
    Pi.disjoint_iff.mpr fun _ ↦ Prop.disjoint_iff.mpr fun ⟨hE, hN⟩ ↦
      hA.ne_empty (a_e_contrary hE hN)

theorem subalternation_a_i (hA : A.Nonempty) : every A B → Det.some A B :=
  (square_relations hA).subalternAI B

/-! ### Left monotonicity and smoothness ([peters-westerstahl-2006]) -/

theorem upSE_some : (Det.some : Det α).UpSEMon := restrictorMonotone_some.upSE

theorem upSW_some : (Det.some : Det α).UpSWMon := restrictorMonotone_some.upSW

theorem downNW_every : (every : Det α).DownNWMon := restrictorAntitone_every.downNW

theorem downNE_every : (every : Det α).DownNEMon := restrictorAntitone_every.downNE

theorem downNW_no : (no : Det α).DownNWMon := restrictorAntitone_no.downNW

theorem downNE_no : (no : Det α).DownNEMon := restrictorAntitone_no.downNE

theorem downNE_some : (Det.some : Det α).DownNEMon :=
  fun _ _ _ _ h ⟨x, hx⟩ ↦ ⟨x, h hx, hx.2⟩

theorem smooth_some : (Det.some : Det α).Smooth := ⟨downNE_some, upSE_some⟩

theorem upSE_every : (every : Det α).UpSEMon :=
  fun _ _ _ _ h₂ h _ hx ↦ Classical.byContradiction fun hB ↦ hB (h (h₂ ⟨hx, hB⟩))

theorem smooth_every : (every : Det α).Smooth := ⟨downNE_every, upSE_every⟩

theorem coSmooth_no : (no : Det α).CoSmooth :=
  ⟨downNW_no, fun _ _ _ _ h₂ h _ hx hB ↦ h (h₂ ⟨hx, hB⟩) hB⟩

/-! ### Barwise and Cooper's universals -/

/-- Barwise and Cooper's monotonicity constraint is right continuity: a quantifier is a
conjunction of monotone quantifiers exactly when it holds at every scope between two at which it
holds, Thijsse's observation reported by [van-benthem-1984]. -/
theorem satisfiesUniversals_iff {d : Det α} :
    d.SatisfiesUniversals ↔ d.Conservative ∧ d.RightContinuous := by
  refine and_congr_right fun _ ↦ ⟨fun h A B B₁ B₂ h₁ h₂ hq₁ hq₂ ↦ ?_, fun h A ↦ ?_⟩
  · obtain ⟨Q₁, Q₂, hm₁, hm₂, he⟩ := h A
    simp only [he, Pi.inf_apply, inf_Prop_eq] at hq₁ hq₂ ⊢
    exact ⟨hm₁.elim (fun hm ↦ hm h₁ hq₁.1) fun hm ↦ hm h₂ hq₂.1,
      hm₂.elim (fun hm ↦ hm h₁ hq₁.2) fun hm ↦ hm h₂ hq₂.2⟩
  · refine ⟨fun B ↦ ∃ B' ≤ B, d A B', fun B ↦ ∃ B', B ≤ B' ∧ d A B',
      .inl fun _ _ hBC ⟨B', hB', hq⟩ ↦ ⟨B', hB'.trans hBC, hq⟩,
      .inr fun _ _ hBC ⟨B', hB', hq⟩ ↦ ⟨B', hBC.trans hB', hq⟩, funext fun B ↦ propext ?_⟩
    exact ⟨fun hq ↦ ⟨⟨B, le_rfl, hq⟩, B, le_rfl, hq⟩,
      fun ⟨⟨B₁, h₁, hq₁⟩, B₂, h₂, hq₂⟩ ↦ h A B B₁ B₂ h₁ h₂ hq₁ hq₂⟩

theorem satisfiesUniversals_some : (Det.some : Det α).SatisfiesUniversals :=
  satisfiesUniversals_iff.2 ⟨conservative_some, scopeMonotone_some.rightContinuous⟩

theorem satisfiesUniversals_every : (every : Det α).SatisfiesUniversals :=
  satisfiesUniversals_iff.2 ⟨conservative_every, scopeMonotone_every.rightContinuous⟩

theorem satisfiesUniversals_no : (no : Det α).SatisfiesUniversals :=
  satisfiesUniversals_iff.2 ⟨conservative_no, scopeAntitone_no.rightContinuous⟩

end Quantifier.Det
