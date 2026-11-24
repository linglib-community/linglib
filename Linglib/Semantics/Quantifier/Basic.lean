module

public import Linglib.Semantics.Quantifier.Defs
public import Linglib.Semantics.Quantifier.Conservative
public import Linglib.Semantics.Quantifier.Monotone
public import Linglib.Semantics.Reference.Iota
public import Mathlib.Order.CompleteLattice.Basic

/-!
# The determiners *every*, *some*, *no* and *the*

This file defines the denotations of the determiners *every*, *some*, *no* and *the*. For a
restrictor `A` and a scope `B`, both sets of individuals:

* `every A B` means that `A ⊆ B`;
* `Det.some A B` means that `A ∩ B` is nonempty;
* `no A B` means that `A ⊆ Bᶜ`, that is, that `A` and `B` are disjoint;
* `the A B` means that `A` has exactly one member and that member is in `B`.

We prove how the four are related by negation, how each depends on the restrictor and on the
scope, and which of the properties of determiner denotations defined in `Quantifier/Defs.lean`
each one has.

The counting determiners, such as *most* and *few*, are in `Quantifier/Counting.lean`. The square
of opposition of `every`, `no`, `some` and *not every* is in `Quantifier/Square.lean`.

## Main definitions

* `Quantifier.Det.every`, `Quantifier.Det.some`, `Quantifier.Det.no`, `Quantifier.Det.the`: the
  four determiner denotations.
* `Quantifier.Det.someOrderEmbedding`, `Quantifier.Det.everyOrderEmbedding`,
  `Quantifier.Det.noOrderEmbedding`: each determiner as an order embedding of the restrictors
  into the quantifiers; `every` and `no` reverse the order.

## Main results

* `Quantifier.Det.no_iff_not_some`, `Quantifier.Det.dual_every`: `no` is the complement of
  `Det.some`, and `Det.some` is the dual of `every`.
* `Quantifier.Det.exists_eq_every_iff`: a quantifier is `every A` for some `A` if and only if it
  commutes with arbitrary intersections of scopes.
* `Quantifier.Det.exists_eq_some_iff`: a quantifier is `Det.some A` for some `A` if and only if
  it commutes with arbitrary unions of scopes.
* `Quantifier.Det.exists_eq_no_iff`: a quantifier is `no A` for some `A` if and only if it holds
  of a union of scopes exactly when it holds of each of them.
* `Quantifier.Det.disjoint_every_no_iff`: `every A` and `no A` are disjoint if and only if `A` is
  nonempty.

## References

* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [partee-1987]
* [russell-1905]
* [van-benthem-1984]
-/

@[expose] public section

namespace Quantifier

variable {α : Type*}

namespace Det

variable {A A' B : Set α}

/-! ### Definitions -/

/-- `every A B` means that `A ⊆ B`: every member of the restrictor is in the scope. -/
def every : Det α := fun A B ↦ A ⊆ B

/-- `Det.some A B` means that `A ∩ B` is nonempty: some member of the restrictor is in the
scope. -/
protected def some : Det α := fun A B ↦ (A ∩ B).Nonempty

/-- `no A B` means that `A ⊆ Bᶜ`: no member of the restrictor is in the scope. -/
def no : Det α := fun A B ↦ A ⊆ Bᶜ

/-- `the A B` means that `A` has exactly one member and that member is in `B`. This is the
singular definite of [russell-1905]. -/
def the : Det α := fun A B ↦ ∃ x, (∀ y, y ∈ A ↔ y = x) ∧ x ∈ B

section Decidable

variable [Fintype α] [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]

instance : Decidable (every A B) := inferInstanceAs (Decidable (∀ _, _))

instance : Decidable (Det.some A B) := inferInstanceAs (Decidable (∃ _, _ ∧ _))

instance : Decidable (no A B) := inferInstanceAs (Decidable (∀ _, _))

end Decidable

/-! ### Basic lemmas -/

theorem every_iff_le : every A B ↔ A ≤ B := .rfl

theorem no_iff_le_compl : no A B ↔ A ≤ Bᶜ := .rfl

theorem no_iff_disjoint : no A B ↔ Disjoint A B := Set.subset_compl_iff_disjoint_right

theorem no_iff_not_some : no A B ↔ ¬ Det.some A B :=
  no_iff_disjoint.trans <| Set.disjoint_iff_inter_eq_empty.trans Set.not_nonempty_iff_eq_empty.symm

theorem some_iff_not_disjoint : Det.some A B ↔ ¬ Disjoint A B :=
  Set.not_disjoint_iff_nonempty_inter.symm

@[simp] theorem every_univ_iff : every Set.univ B ↔ B = Set.univ := Set.univ_subset_iff

@[simp] theorem some_univ_iff : Det.some Set.univ B ↔ B.Nonempty := by simp [Det.some]

@[simp] theorem no_univ_iff : no Set.univ B ↔ B = ∅ := by simp [no, Set.univ_subset_iff]

@[simp] theorem every_empty : every (∅ : Set α) = ⊤ := by funext B; simp [every]

@[simp] theorem some_empty : Det.some (∅ : Set α) = ⊥ := by funext B; simp [Det.some]

@[simp] theorem no_empty : no (∅ : Set α) = ⊤ := by funext B; simp [no]

@[simp] theorem every_apply_empty : every A ∅ ↔ A = ∅ := Set.subset_empty_iff

@[simp] theorem some_self_iff : Det.some A A ↔ A.Nonempty := by rw [Det.some, Set.inter_self]

@[simp] theorem no_self_iff : no A A ↔ A = ∅ := no_iff_disjoint.trans disjoint_self

/-! ### The definite -/

theorem the_iff : the A B ↔ (∃! x, x ∈ A) ∧ A ⊆ B := by
  constructor
  · rintro ⟨x, hx, hB⟩
    exact ⟨⟨x, (hx x).2 rfl, fun y hy ↦ (hx y).1 hy⟩, fun y hy ↦ (hx y).1 hy ▸ hB⟩
  · rintro ⟨⟨x, hx, huniq⟩, hB⟩
    exact ⟨x, fun y ↦ ⟨huniq y, fun h ↦ h ▸ hx⟩, hB hx⟩

theorem the_iff_exists_mem_iota : the A B ↔ ∃ x ∈ iota A, x ∈ B :=
  exists_congr fun _ ↦ and_congr_left' <|
    Set.ext_iff.symm.trans mem_iota_iff_eq_singleton.symm

/-- If `iota A` is defined and equal to `a`, then `the A` is the quantifier of the individual
`a` ([partee-1987]). -/
theorem the_eq_individual {a : α} (h : a ∈ iota A) : the A = individual a :=
  funext fun _ ↦ propext <| the_iff_exists_mem_iota.trans
    ⟨fun ⟨_, hx, hB⟩ ↦ Part.mem_unique h hx ▸ hB, fun hB ↦ ⟨a, h, hB⟩⟩

/-- If `iota A` is undefined, then `the A` holds of no scope ([partee-1987]). -/
theorem the_eq_bot (h : ¬ (iota A).Dom) : the A = ⊥ :=
  funext fun _ ↦ propext <| the_iff_exists_mem_iota.trans
    ⟨fun ⟨_, hx, _⟩ ↦ h (Part.dom_iff_mem.2 ⟨_, hx⟩), False.elim⟩

theorem the_le_every : the A ≤ every A := fun _ h ↦ (the_iff.1 h).2

theorem the_le_some : the A ≤ Det.some A := fun _ ⟨x, hx, hB⟩ ↦ ⟨x, (hx x).2 rfl, hB⟩

theorem scopeMonotone_the : (the : Det α).ScopeMonotone :=
  fun _ _ _ h ⟨x, hA, hB⟩ ↦ ⟨x, hA, h hB⟩

theorem conservative_the : (the : Det α).Conservative := fun A B ↦ by
  simp only [the_iff, Set.subset_inter_iff, subset_rfl, true_and]

/-! ### Negation and duality

*No* is the inner negation of *every* and the complement of *some*, and *some* is the dual of
*every*. -/

theorem innerNeg_every : (every : Det α).innerNeg = no := rfl

theorem innerNeg_no : (no : Det α).innerNeg = every := by
  rw [← innerNeg_every, innerNeg_innerNeg]

theorem compl_some : (Det.some : Det α)ᶜ = no := by
  funext A B; exact propext no_iff_not_some.symm

theorem dual_every : (every : Det α).dual = Det.some := by
  rw [dual, innerNeg_every, ← compl_some, compl_compl]

theorem dual_some : (Det.some : Det α).dual = every := by
  rw [← dual_every, dual_dual]

/-! ### Dependence on the restrictor

`Det.some` is monotone in the restrictor and sends unions of restrictors to joins. `every` and
`no` are antitone in the restrictor and send unions to meets. All three are injective. -/

theorem every_le_every_iff : every A ≤ every A' ↔ A' ⊆ A :=
  ⟨fun h ↦ h A subset_rfl, fun h _ hB ↦ h.trans hB⟩

theorem some_le_some_iff : Det.some A ≤ Det.some A' ↔ A ⊆ A' :=
  ⟨fun h x hx ↦ let ⟨_, hy, hxy⟩ := h {x} ⟨x, hx, rfl⟩; Set.eq_of_mem_singleton hxy ▸ hy,
    fun h B hB ↦ hB.mono (Set.inter_subset_inter_left B h)⟩

theorem no_le_no_iff : no A ≤ no A' ↔ A' ⊆ A :=
  ⟨fun h ↦ (h Aᶜ (compl_compl A).ge).trans (compl_compl A).le, fun h _ hB ↦ h.trans hB⟩

theorem every_injective : Function.Injective (every : Det α) := fun A B h ↦
  subset_antisymm ((congrFun h B).mpr subset_rfl) ((congrFun h A).mp subset_rfl)

theorem some_injective : Function.Injective (Det.some : Det α) := fun _ _ h ↦
  subset_antisymm (some_le_some_iff.1 h.le) (some_le_some_iff.1 h.ge)

theorem no_injective : Function.Injective (no : Det α) := fun _ _ h ↦
  subset_antisymm (no_le_no_iff.1 h.ge) (no_le_no_iff.1 h.le)

/-- `Det.some` as an order embedding of the restrictors into the quantifiers. -/
def someOrderEmbedding : Set α ↪o Quantifier α :=
  .ofMapLEIff Det.some fun _ _ ↦ some_le_some_iff

/-- `every` as an order embedding of the restrictors, with the reverse order, into the
quantifiers. -/
def everyOrderEmbedding : (Set α)ᵒᵈ ↪o Quantifier α :=
  .ofMapLEIff (fun A ↦ every A.ofDual) fun _ _ ↦ every_le_every_iff

/-- `no` as an order embedding of the restrictors, with the reverse order, into the
quantifiers. -/
def noOrderEmbedding : (Set α)ᵒᵈ ↪o Quantifier α :=
  .ofMapLEIff (fun A ↦ no A.ofDual) fun _ _ ↦ no_le_no_iff

@[simp] theorem coe_someOrderEmbedding : ⇑(someOrderEmbedding (α := α)) = Det.some := rfl

@[simp] theorem everyOrderEmbedding_apply (A : (Set α)ᵒᵈ) :
    everyOrderEmbedding A = every A.ofDual := rfl

@[simp] theorem noOrderEmbedding_apply (A : (Set α)ᵒᵈ) : noOrderEmbedding A = no A.ofDual := rfl

/-- `Det.some` sends a union of restrictors to a join. -/
theorem some_union (A A' : Set α) : Det.some (A ∪ A') = Det.some A ⊔ Det.some A' := by
  funext B; simp [Det.some, Set.union_inter_distrib_right, Set.union_nonempty]

/-- `every` sends a union of restrictors to a meet. -/
theorem every_union (A A' : Set α) : every (A ∪ A') = every A ⊓ every A' := by
  funext B; simp [every, Set.union_subset_iff]

/-- `no` sends a union of restrictors to a meet. -/
theorem no_union (A A' : Set α) : no (A ∪ A') = no A ⊓ no A' := by
  funext B; simp [no, Set.union_subset_iff]

theorem some_iUnion {ι : Sort*} (A : ι → Set α) : Det.some (⋃ i, A i) = ⨆ i, Det.some (A i) := by
  funext B; simp [Det.some, Set.iUnion_inter]

theorem every_iUnion {ι : Sort*} (A : ι → Set α) : every (⋃ i, A i) = ⨅ i, every (A i) := by
  funext B; simp [every, Set.iUnion_subset_iff]

theorem no_iUnion {ι : Sort*} (A : ι → Set α) : no (⋃ i, A i) = ⨅ i, no (A i) := by
  funext B; simp [no, Set.iUnion_subset_iff]

/-- The quantifier of the individual `a` is `every {a}`. -/
theorem _root_.Quantifier.individual_eq_every (a : α) : individual a = every {a} := by
  funext B; simp [individual, every]

theorem restrictorAntitone_every : (every : Det α).RestrictorAntitone :=
  fun _ _ _ hA h ↦ hA.trans h

theorem restrictorMonotone_some : (Det.some : Det α).RestrictorMonotone :=
  fun B _ _ hA h ↦ h.mono (Set.inter_subset_inter_left B hA)

theorem restrictorAntitone_no : (no : Det α).RestrictorAntitone := fun _ _ _ hA h ↦ hA.trans h

theorem leftAntiAdditive_every : (every : Det α).LeftAntiAdditive :=
  fun _ _ _ ↦ propext Set.union_subset_iff

theorem leftAntiAdditive_no : (no : Det α).LeftAntiAdditive :=
  fun _ _ _ ↦ propext Set.union_subset_iff

/-! ### Left monotonicity and smoothness -/

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

/-! ### Dependence on the scope

`every A` and `Det.some A` are monotone in the scope and `no A` is antitone. `every A` commutes
with arbitrary intersections of scopes and `Det.some A` with arbitrary unions. -/

theorem scopeMonotone_every : (every : Det α).ScopeMonotone := fun _ _ _ h h' ↦ h'.trans h

theorem scopeMonotone_some : (Det.some : Det α).ScopeMonotone :=
  fun A _ _ h h' ↦ h'.mono (Set.inter_subset_inter_right A h)

theorem scopeAntitone_no : (no : Det α).ScopeAntitone :=
  fun _ _ _ h h' ↦ h'.trans (Set.compl_subset_compl.2 h)

theorem not_scopeAntitone_some [Nonempty α] : ¬ (Det.some : Det α).ScopeAntitone := fun h ↦
  let ⟨x⟩ := ‹Nonempty α›
  (h Set.univ (Set.empty_subset _) ⟨x, Set.mem_univ x, Set.mem_univ x⟩).ne_empty (Set.inter_empty _)

theorem not_scopeAntitone_every [Nonempty α] : ¬ (every : Det α).ScopeAntitone := fun h ↦
  let ⟨x⟩ := ‹Nonempty α›
  Set.notMem_empty x (h Set.univ (Set.empty_subset _) subset_rfl (Set.mem_univ x))

theorem monotone_every (A : Set α) : Monotone (every A) := scopeMonotone_every A

theorem monotone_some (A : Set α) : Monotone (Det.some A) := scopeMonotone_some A

theorem antitone_no (A : Set α) : Antitone (no A) := scopeAntitone_no A

theorem rightAntiAdditive_no : (no : Det α).RightAntiAdditive := fun A ↦
  isAntiAdditive_iff.2 fun B B' ↦ by rw [no, Set.compl_union, Set.subset_inter_iff]; rfl

theorem scopeIntersective_every : (every : Det α).ScopeIntersective :=
  fun _ _ _ ↦ Set.subset_inter

theorem filtrating_every : (every : Det α).Filtrating :=
  ⟨scopeMonotone_every, scopeIntersective_every⟩

theorem every_sInter (A : Set α) (S : Set (Set α)) : every A (⋂₀ S) ↔ ∀ B ∈ S, every A B :=
  Set.subset_sInter_iff

theorem some_sUnion (A : Set α) (S : Set (Set α)) :
    Det.some A (⋃₀ S) ↔ ∃ B ∈ S, Det.some A B := by
  simp only [some_iff_not_disjoint, Set.disjoint_sUnion_right, not_forall, exists_prop]

theorem no_sUnion (A : Set α) (S : Set (Set α)) : no A (⋃₀ S) ↔ ∀ B ∈ S, no A B := by
  simp only [no_iff_disjoint, Set.disjoint_sUnion_right]

theorem every_eq_sInf_image (A B : Set α) : every A B = sInf ((· ∈ B) '' A) := by
  rw [sInf_Prop_eq, Set.forall_mem_image]; rfl

theorem some_eq_sSup_image (A B : Set α) : Det.some A B = sSup ((· ∈ B) '' A) := by
  rw [sSup_Prop_eq, Set.exists_mem_image]; rfl

theorem no_eq_compl_sSup_image (A B : Set α) : no A B = (sSup ((· ∈ B) '' A))ᶜ := by
  rw [← some_eq_sSup_image]; exact propext no_iff_not_some

/-! ### Characterization by intersections and unions of scopes

The way each of the three quantifiers treats arbitrary intersections or unions of scopes
characterizes it. The restrictor of `every A` is the intersection of its scopes, and the
restrictor of `Det.some A` is the set of `x` such that `{x}` is a scope. -/

theorem sInter_setOf_every (A : Set α) : ⋂₀ {B | every A B} = A :=
  subset_antisymm (Set.sInter_subset_of_mem (Set.Subset.refl A : every A A))
    (Set.subset_sInter fun _ h ↦ h)

/-- A quantifier is `every A` for some `A` if and only if it commutes with arbitrary
intersections of scopes. -/
theorem exists_eq_every_iff {Q : Quantifier α} :
    (∃ A, Q = every A) ↔ ∀ S : Set (Set α), Q (⋂₀ S) ↔ ∀ B ∈ S, Q B := by
  refine ⟨?_, fun h ↦ ⟨⋂₀ {B | Q B}, funext fun B ↦ propext
    ⟨fun hB ↦ Set.sInter_subset_of_mem hB, fun hB ↦ ?_⟩⟩⟩
  · rintro ⟨A, rfl⟩ S
    exact every_sInter A S
  · have h₁ : Q (⋂₀ {B | Q B}) := (h _).2 fun _ hB ↦ hB
    rw [← Set.inter_eq_left.2 hB, ← Set.sInter_pair] at h₁
    exact (h _).1 h₁ B (Set.mem_insert_of_mem _ rfl)

/-- A quantifier is `Det.some A` for some `A` if and only if it commutes with arbitrary unions
of scopes. -/
theorem exists_eq_some_iff {Q : Quantifier α} :
    (∃ A, Q = Det.some A) ↔ ∀ S : Set (Set α), Q (⋃₀ S) ↔ ∃ B ∈ S, Q B := by
  refine ⟨?_, fun h ↦ ⟨{x | Q {x}}, funext fun B ↦ propext ?_⟩⟩
  · rintro ⟨A, rfl⟩ S
    exact some_sUnion A S
  · have hB := h ((fun x ↦ ({x} : Set α)) '' B)
    rw [Set.sUnion_image, Set.biUnion_of_singleton, Set.exists_mem_image] at hB
    exact hB.trans ⟨fun ⟨x, hx, hQ⟩ ↦ ⟨x, hQ, hx⟩, fun ⟨x, hQ, hx⟩ ↦ ⟨x, hx, hQ⟩⟩

/-- A quantifier is `no A` for some `A` if and only if it holds of a union of scopes exactly
when it holds of each of them. -/
theorem exists_eq_no_iff {Q : Quantifier α} :
    (∃ A, Q = no A) ↔ ∀ S : Set (Set α), Q (⋃₀ S) ↔ ∀ B ∈ S, Q B := by
  have h : (∃ A, Q = no A) ↔ ∃ A, Qᶜ = Det.some A :=
    exists_congr fun A ↦ by rw [← compl_some, compl_eq_comm, eq_comm]; rfl
  rw [h, exists_eq_some_iff]
  refine forall_congr' fun S ↦ ?_
  simp only [Pi.compl_apply, compl_iff_not, not_iff_comm (b := ∃ B ∈ S, ¬ Q B), not_exists,
    not_and, not_not]
  exact iff_comm

/-! ### Conservativity -/

theorem conservative_every : (every : Det α).Conservative :=
  fun _ _ ↦ (Set.subset_inter_iff.trans (and_iff_right subset_rfl)).symm

theorem conservative_some : (Det.some : Det α).Conservative := fun A B ↦ by
  show (A ∩ B).Nonempty ↔ (A ∩ (A ∩ B)).Nonempty
  rw [← Set.inter_assoc, Set.inter_self]

theorem conservative_no : (no : Det α).Conservative := fun A B ↦
  no_iff_not_some.trans <| (not_congr (conservative_some A B)).trans no_iff_not_some.symm

/-! ### Relational properties

A determiner denotation is a relation between sets. `every` is reflexive, transitive and
antisymmetric; `Det.some` and `no` are symmetric. -/

theorem positiveStrong_every : (every : Det α).PositiveStrong := fun _ ↦ subset_rfl

instance isTrans_every : IsTrans _ (every : Det α) := ⟨fun _ _ _ h₁ h₂ ↦ h₁.trans h₂⟩

instance antisymm_every : Std.Antisymm (every : Det α) := ⟨fun _ _ ↦ Set.Subset.antisymm⟩

instance symm_some : Std.Symm (Det.some : Det α) :=
  ⟨fun A B h ↦ by rwa [Det.some, Set.inter_comm]⟩

instance symm_no : Std.Symm (no : Det α) := ⟨fun _ _ h ↦ Set.subset_compl_comm.1 h⟩

theorem intersective_some : (Det.some : Det α).Intersective :=
  fun _ _ _ _ h ↦ by rw [Det.some, Det.some, h]

theorem intersective_no : (no : Det α).Intersective := fun A B A' B' h ↦
  no_iff_not_some.trans <| (not_congr (intersective_some A B A' B' h)).trans no_iff_not_some.symm

theorem coIntersective_every : (every : Det α).CoIntersective := fun A B A' B' h ↦ by
  change A ≤ B ↔ A' ≤ B'
  rw [← sdiff_eq_bot_iff, ← sdiff_eq_bot_iff, h]

theorem quasiReflexive_some : (Det.some : Det α).QuasiReflexive :=
  fun _ _ ⟨x, hx⟩ ↦ ⟨x, hx.1, hx.1⟩

theorem quasiUniversal_no : (no : Det α).QuasiUniversal := fun _ _ h _ hx ↦ absurd hx (h hx)

/-! ### Barwise and Cooper's universals -/

theorem satisfiesUniversals_some : (Det.some : Det α).SatisfiesUniversals :=
  satisfiesUniversals_iff.2 ⟨conservative_some, scopeMonotone_some.rightContinuous⟩

theorem satisfiesUniversals_every : (every : Det α).SatisfiesUniversals :=
  satisfiesUniversals_iff.2 ⟨conservative_every, scopeMonotone_every.rightContinuous⟩

theorem satisfiesUniversals_no : (no : Det α).SatisfiesUniversals :=
  satisfiesUniversals_iff.2 ⟨conservative_no, scopeAntitone_no.rightContinuous⟩

/-! ### Existential import

`every A` and `no A` both hold of every scope when `A` is empty. For a nonempty `A` they cannot
both hold, and `every A` entails `Det.some A`. -/

theorem eq_empty_of_every_of_no (hA : every A B) (hE : no A B) : A = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hx ↦ hE hx (hA hx)

theorem disjoint_every_no_iff : Disjoint (every A) (no A) ↔ A.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  refine ⟨fun h hA ↦ ?_, fun hA ↦ Pi.disjoint_iff.mpr fun _ ↦ Prop.disjoint_iff.mpr
    fun ⟨h₁, h₂⟩ ↦ hA (eq_empty_of_every_of_no h₁ h₂)⟩
  subst hA
  exact Prop.disjoint_iff.1 (Pi.disjoint_iff.1 h ∅) ⟨Set.empty_subset _, Set.empty_subset _⟩

theorem every_le_some (hA : A.Nonempty) : every A ≤ Det.some A :=
  fun _ h ↦ let ⟨x, hx⟩ := hA; ⟨x, hx, h hx⟩

end Det

end Quantifier
