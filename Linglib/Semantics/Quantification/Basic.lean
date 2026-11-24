module

public import Linglib.Semantics.Quantification.Defs
public import Linglib.Semantics.Quantification.Properties
public import Linglib.Logic.Aristotelian.Square
public import Linglib.Semantics.Reference.Iota
public import Mathlib.Order.CompleteLattice.Basic

/-!
# The determiners *every*, *some*, *no* and *the*

This file defines the determiner denotations *every* (`A ⊆ B`), *some* (`A ∩ B` nonempty), *no*
(`A ⊆ Bᶜ`) and the Russellian *the*, whose truth conditions need no counting. The counting
quantifiers such as *most* and *few* are in `Quantification/Counting.lean`.

At a restrictor `A`, the quantifier `every A` is the principal filter of `A`: the sets that
include `A`. It commutes with arbitrary intersections of scopes, and the quantifiers that do so
are exactly the `every A`, each at the intersection of its scopes. Dually `some A` commutes with
arbitrary unions, `no A` turns them into conjunctions, and these properties characterize the two.
In the restrictor, *some* is an order embedding of the sets into the quantifiers, and *every* and
*no* are order embeddings of the sets with the reverse order.

A quantifier `Q` spans the square of opposition of `Q`, its inner negation, its dual and its
complement. Its diagonals are contradictory for every `Q`, and the remaining relations of the
classical square hold exactly when `Q ≤ Q.dual`. For a quantifier whose scopes form a filter that
is `¬ Q ∅`, so the square of `every A` has them exactly when `A` is nonempty, and its universals
can both fail exactly when `A` has two members.

## Main definitions

* `every`, `Det.some`, `no`, `the`: the propositional denotations.
* `someOrderEmbedding`, `everyOrderEmbedding`, `noOrderEmbedding`: the three determiners as order
  embeddings of the restrictors.
* `Quantifier.square`: the square of opposition that a quantifier spans.
* `square`: the square of opposition of `every`, `no`, `some` and `not every` at a restrictor.

## Main results

* `exists_eq_every_iff`, `exists_eq_some_iff`, `exists_eq_no_iff`: the quantifiers `every A`,
  `some A` and `no A` are those that commute with arbitrary intersections, commute with arbitrary
  unions, and turn arbitrary unions into conjunctions.
* `every_eq_sInf_image`, `some_eq_sSup_image`, `no_eq_compl_sSup_image`: the three determiners
  are the infimum, the supremum and the complement of the supremum of the scope over the
  restrictor.
* `no_iff_disjoint`, `no_iff_not_some`: *no* is disjointness, the complement of *some*.
* `squareRelations_square_iff`: a quantifier's square has the relations of the classical square
  exactly when the quantifier entails its dual.
* `squareRelations_square`: the square at a restrictor has them exactly when the restrictor is
  nonempty.
* `isContrary_every_no_iff`: `every A` and `no A` are contrary exactly when `A` has two members.

## Implementation notes

The square at a restrictor is stated with `Det.some A` at its particular affirmative corner and
is equal to the square that `every A` spans, whose corner is the dual of `every A`
(`square_eq`).

## References

* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [partee-1987]
* [peters-westerstahl-2006]
* [russell-1905]
* [van-benthem-1984]
-/

@[expose] public section

namespace Quantifier

variable {α : Type*}

namespace Det

variable {A A' B : Set α}

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

theorem the_iff_exists_mem_iota : the A B ↔ ∃ x ∈ iota A, x ∈ B :=
  exists_congr fun _ ↦ and_congr_left' <|
    Set.ext_iff.symm.trans mem_iota_iff_eq_singleton.symm

/-- *The `A`* is the lift of `iota A` where `iota A` is defined ([partee-1987], §3.2). -/
theorem the_eq_individual {a : α} (h : a ∈ iota A) : the A = individual a :=
  funext fun _ ↦ propext <| the_iff_exists_mem_iota.trans
    ⟨fun ⟨_, hx, hB⟩ ↦ Part.mem_unique h hx ▸ hB, fun hB ↦ ⟨a, h, hB⟩⟩

/-- *The `A`* is the empty quantifier where `iota A` is undefined ([partee-1987], §3.2). -/
theorem the_eq_bot (h : ¬ (iota A).Dom) : the A = ⊥ :=
  funext fun _ ↦ propext <| the_iff_exists_mem_iota.trans
    ⟨fun ⟨_, hx, _⟩ ↦ h (Part.dom_iff_mem.2 ⟨_, hx⟩), False.elim⟩

theorem the_le_every : the A ≤ every A := fun _ h ↦ (the_iff.1 h).2

theorem the_le_some : the A ≤ Det.some A := fun _ ⟨x, hx, hB⟩ ↦ ⟨x, (hx x).2 rfl, hB⟩

theorem every_iff_le : every A B ↔ A ≤ B := .rfl

theorem every_injective : Function.Injective (every : Det α) := fun A B h ↦
  subset_antisymm ((congrFun h B).mpr subset_rfl) ((congrFun h A).mp subset_rfl)

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

/-! ### The restrictor

*Some* preserves the order of restrictors and turns their unions into joins; *every* and *no*
reverse the order and turn unions into meets. Each is injective. -/

theorem every_le_every_iff : every A ≤ every A' ↔ A' ⊆ A :=
  ⟨fun h ↦ h A subset_rfl, fun h _ hB ↦ h.trans hB⟩

theorem some_le_some_iff : Det.some A ≤ Det.some A' ↔ A ⊆ A' :=
  ⟨fun h x hx ↦ let ⟨_, hy, hxy⟩ := h {x} ⟨x, hx, rfl⟩; Set.eq_of_mem_singleton hxy ▸ hy,
    fun h B hB ↦ hB.mono (Set.inter_subset_inter_left B h)⟩

theorem no_le_no_iff : no A ≤ no A' ↔ A' ⊆ A :=
  ⟨fun h ↦ (h Aᶜ (compl_compl A).ge).trans (compl_compl A).le, fun h _ hB ↦ h.trans hB⟩

theorem some_injective : Function.Injective (Det.some : Det α) := fun _ _ h ↦
  subset_antisymm (some_le_some_iff.1 h.le) (some_le_some_iff.1 h.ge)

theorem no_injective : Function.Injective (no : Det α) := fun _ _ h ↦
  subset_antisymm (no_le_no_iff.1 h.ge) (no_le_no_iff.1 h.le)

/-- *Some* as an order embedding of the restrictors into the quantifiers. -/
def someOrderEmbedding : Set α ↪o Quantifier α :=
  .ofMapLEIff Det.some fun _ _ ↦ some_le_some_iff

/-- *Every* as an order embedding of the restrictors, in the reverse order, into the
quantifiers. -/
def everyOrderEmbedding : (Set α)ᵒᵈ ↪o Quantifier α :=
  .ofMapLEIff (fun A ↦ every A.ofDual) fun _ _ ↦ every_le_every_iff

/-- *No* as an order embedding of the restrictors, in the reverse order, into the quantifiers. -/
def noOrderEmbedding : (Set α)ᵒᵈ ↪o Quantifier α :=
  .ofMapLEIff (fun A ↦ no A.ofDual) fun _ _ ↦ no_le_no_iff

@[simp] theorem coe_someOrderEmbedding : ⇑(someOrderEmbedding (α := α)) = Det.some := rfl

@[simp] theorem everyOrderEmbedding_apply (A : (Set α)ᵒᵈ) :
    everyOrderEmbedding A = every A.ofDual := rfl

@[simp] theorem noOrderEmbedding_apply (A : (Set α)ᵒᵈ) : noOrderEmbedding A = no A.ofDual := rfl

/-- *Some* turns a union of restrictors into a join. -/
theorem some_union (A A' : Set α) : Det.some (A ∪ A') = Det.some A ⊔ Det.some A' := by
  funext B; simp [Det.some, Set.union_inter_distrib_right, Set.union_nonempty]

/-- *Every* turns a union of restrictors into a meet. -/
theorem every_union (A A' : Set α) : every (A ∪ A') = every A ⊓ every A' := by
  funext B; simp [every, Set.union_subset_iff]

/-- *No* turns a union of restrictors into a meet. -/
theorem no_union (A A' : Set α) : no (A ∪ A') = no A ⊓ no A' := by
  funext B; simp [no, Set.union_subset_iff]

theorem some_iUnion {ι : Sort*} (A : ι → Set α) : Det.some (⋃ i, A i) = ⨆ i, Det.some (A i) := by
  funext B; simp [Det.some, Set.iUnion_inter]

theorem every_iUnion {ι : Sort*} (A : ι → Set α) : every (⋃ i, A i) = ⨅ i, every (A i) := by
  funext B; simp [every, Set.iUnion_subset_iff]

theorem no_iUnion {ι : Sort*} (A : ι → Set α) : no (⋃ i, A i) = ⨅ i, no (A i) := by
  funext B; simp [no, Set.iUnion_subset_iff]

/-- The Montague lift of `a` is *every* on `{a}`. -/
theorem _root_.Quantifier.individual_eq_every (a : α) : individual a = every {a} := by
  funext B; simp [individual, every]

section Decidable

variable [Fintype α] [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]

instance : Decidable (every A B) := inferInstanceAs (Decidable (∀ _, _))

instance : Decidable (Det.some A B) := inferInstanceAs (Decidable (∃ _, _ ∧ _))

instance : Decidable (no A B) := inferInstanceAs (Decidable (∀ _, _))

end Decidable

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

/-! ### Arbitrary intersections and unions of scopes

`every A` commutes with arbitrary intersections of scopes and `some A` with arbitrary unions,
and `no A` turns a union of scopes into a conjunction. Each property characterizes the
quantifiers of that form, and recovers the restrictor: as the intersection of the scopes of
`every A`, and as the elements whose singleton is a scope of `some A`. -/

theorem every_sInter (A : Set α) (S : Set (Set α)) : every A (⋂₀ S) ↔ ∀ B ∈ S, every A B :=
  Set.subset_sInter_iff

theorem some_sUnion (A : Set α) (S : Set (Set α)) :
    Det.some A (⋃₀ S) ↔ ∃ B ∈ S, Det.some A B := by
  simp only [some_iff_not_disjoint, Set.disjoint_sUnion_right, not_forall, exists_prop]

theorem no_sUnion (A : Set α) (S : Set (Set α)) : no A (⋃₀ S) ↔ ∀ B ∈ S, no A B := by
  simp only [no_iff_disjoint, Set.disjoint_sUnion_right]

theorem sInter_setOf_every (A : Set α) : ⋂₀ {B | every A B} = A :=
  subset_antisymm (Set.sInter_subset_of_mem (Set.Subset.refl A : every A A))
    (Set.subset_sInter fun _ h ↦ h)

/-- The quantifiers that commute with arbitrary intersections are the quantifiers `every A`. -/
theorem exists_eq_every_iff {Q : Quantifier α} :
    (∃ A, Q = every A) ↔ ∀ S : Set (Set α), Q (⋂₀ S) ↔ ∀ B ∈ S, Q B := by
  refine ⟨?_, fun h ↦ ⟨⋂₀ {B | Q B}, funext fun B ↦ propext
    ⟨fun hB ↦ Set.sInter_subset_of_mem hB, fun hB ↦ ?_⟩⟩⟩
  · rintro ⟨A, rfl⟩ S
    exact every_sInter A S
  · have h₁ : Q (⋂₀ {B | Q B}) := (h _).2 fun _ hB ↦ hB
    rw [← Set.inter_eq_left.2 hB, ← Set.sInter_pair] at h₁
    exact (h _).1 h₁ B (Set.mem_insert_of_mem _ rfl)

/-- The quantifiers that commute with arbitrary unions are the quantifiers `some A`. -/
theorem exists_eq_some_iff {Q : Quantifier α} :
    (∃ A, Q = Det.some A) ↔ ∀ S : Set (Set α), Q (⋃₀ S) ↔ ∃ B ∈ S, Q B := by
  refine ⟨?_, fun h ↦ ⟨{x | Q {x}}, funext fun B ↦ propext ?_⟩⟩
  · rintro ⟨A, rfl⟩ S
    exact some_sUnion A S
  · have hB := h ((fun x ↦ ({x} : Set α)) '' B)
    rw [Set.sUnion_image, Set.biUnion_of_singleton, Set.exists_mem_image] at hB
    exact hB.trans ⟨fun ⟨x, hx, hQ⟩ ↦ ⟨x, hQ, hx⟩, fun ⟨x, hQ, hx⟩ ↦ ⟨x, hx, hQ⟩⟩

/-! ### Conservativity and permutation invariance -/

theorem conservative_every : (every : Det α).Conservative :=
  fun _ _ ↦ (Set.subset_inter_iff.trans (and_iff_right subset_rfl)).symm

theorem conservative_some : (Det.some : Det α).Conservative := fun A B ↦ by
  show (A ∩ B).Nonempty ↔ (A ∩ (A ∩ B)).Nonempty
  rw [← Set.inter_assoc, Set.inter_self]

theorem conservative_no : (no : Det α).Conservative := fun A B ↦
  no_iff_not_some.trans <| (not_congr (conservative_some A B)).trans no_iff_not_some.symm

theorem conservative_the : (the : Det α).Conservative := fun A B ↦ by
  simp only [the_iff, Set.subset_inter_iff, subset_rfl, true_and]

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

theorem coIntersective_every : (every : Det α).CoIntersective := fun A B A' B' h ↦ by
  change A ≤ B ↔ A' ≤ B'
  rw [← sdiff_eq_bot_iff, ← sdiff_eq_bot_iff, h]

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

theorem dual_some : (Det.some : Det α).dual = every := by
  rw [← dual_every, dual_dual]

theorem innerNeg_no : (no : Det α).innerNeg = every := by
  rw [← innerNeg_every, innerNeg_innerNeg]

/-- The quantifiers that turn arbitrary unions into conjunctions are the quantifiers `no A`. -/
theorem exists_eq_no_iff {Q : Quantifier α} :
    (∃ A, Q = no A) ↔ ∀ S : Set (Set α), Q (⋃₀ S) ↔ ∀ B ∈ S, Q B := by
  have h : (∃ A, Q = no A) ↔ ∃ A, Qᶜ = Det.some A :=
    exists_congr fun A ↦ by rw [← compl_some, compl_eq_comm, eq_comm]; rfl
  rw [h, exists_eq_some_iff]
  refine forall_congr' fun S ↦ ?_
  simp only [Pi.compl_apply, compl_iff_not, not_iff_comm (b := ∃ B ∈ S, ¬ Q B), not_exists,
    not_and, not_not]
  exact iff_comm

/-! ### Strength -/

theorem positiveStrong_every : (every : Det α).PositiveStrong := fun _ ↦ subset_rfl

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

theorem scopeIntersective_every : (every : Det α).ScopeIntersective :=
  fun _ _ _ ↦ Set.subset_inter

theorem filtrating_every : (every : Det α).Filtrating :=
  ⟨scopeMonotone_every, scopeIntersective_every⟩

end Det

/-! ### The square of a quantifier

A quantifier spans a square of opposition with its inner negation, its dual and its complement.
The diagonals are contradictory whatever the quantifier. The universals are disjoint, and with
that the subalternations and subcontrariety hold, exactly when the quantifier entails its dual;
for a quantifier closed under supersets and intersections of scopes, that is when it does not
hold of the empty set. -/

/-- The square of opposition that a quantifier spans: the quantifier, its inner negation, its
dual and its complement ([peters-westerstahl-2006]). -/
@[simps]
def square (Q : Quantifier α) : Aristotelian.Square (Quantifier α) := ⟨Q, Q.innerNeg, Q.dual, Qᶜ⟩

variable {Q : Quantifier α}

theorem square_eq_ofUniversals (Q : Quantifier α) : Q.square = .ofUniversals Q Q.innerNeg := rfl

/-- The inner negation of a quantifier spans the same square, with the universals exchanged and
the particulars exchanged. -/
theorem square_innerNeg (Q : Quantifier α) : Q.innerNeg.square = Q.square.inner :=
  Aristotelian.Square.ext rfl (innerNeg_innerNeg Q) (congrArg (·ᶜ) (innerNeg_innerNeg Q)) rfl

theorem disjoint_innerNeg_iff : Disjoint Q Q.innerNeg ↔ Q ≤ Q.dual :=
  le_compl_iff_disjoint_right.symm

/-- The square of a quantifier has the relations of the classical square exactly when the
quantifier entails its dual. -/
theorem squareRelations_square_iff : Aristotelian.SquareRelations Q.square ↔ Q ≤ Q.dual :=
  Aristotelian.squareRelations_ofUniversals.trans disjoint_innerNeg_iff

/-- A quantifier closed under supersets and intersections of scopes entails its dual exactly
when it does not hold of the empty set. -/
theorem le_dual_iff_not_apply_empty (hm : Monotone Q) (hi : ∀ B C, Q B → Q C → Q (B ∩ C)) :
    Q ≤ Q.dual ↔ ¬ Q ∅ :=
  ⟨fun h h₀ ↦ h ∅ h₀ (hm (Set.empty_subset _) h₀),
    fun h B hB hB' ↦ h (Set.inter_compl_self B ▸ hi _ _ hB hB')⟩

namespace Det

variable {A B : Set α}

/-! ### The square at a restrictor

At a restrictor `A`, the denotations `every A`, `no A`, `Det.some A` and `everyᶜ A` are the corners
of the square that `every A` spans. Its relations need existential import: at an empty restrictor
`every` and `no` both hold vacuously. -/

/-- At a restrictor `A` the four determiners form a square of opposition. -/
def square (A : Set α) : Aristotelian.Square (Quantifier α) where
  A := every A
  E := no A
  I := Det.some A
  O := (every : Det α)ᶜ A

theorem square_eq (A : Set α) : square A = (every A).square :=
  Aristotelian.Square.ext rfl rfl (congrFun dual_every A).symm rfl

theorem eq_empty_of_every_of_no (hA : every A B) (hE : no A B) : A = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hx ↦ hE hx (hA hx)

/-- The four determiners stand in the relations of the square exactly at a nonempty
restrictor. -/
theorem squareRelations_square : Aristotelian.SquareRelations (square A) ↔ A.Nonempty := by
  rw [square_eq, Quantifier.squareRelations_square_iff,
    le_dual_iff_not_apply_empty (monotone_every A) fun _ _ ↦ Set.subset_inter, every_apply_empty,
    Set.nonempty_iff_ne_empty]

theorem disjoint_every_no_iff : Disjoint (every A) (no A) ↔ A.Nonempty :=
  Aristotelian.squareRelations_ofUniversals.symm.trans <|
  (square_eq A ▸ squareRelations_square (A := A) :)

theorem every_le_some (hA : A.Nonempty) : every A ≤ Det.some A :=
  (squareRelations_square.2 hA).subalternAI

theorem some_inf_compl_every_ne_bot_iff :
    Det.some A ⊓ (every : Det α)ᶜ A ≠ ⊥ ↔ A.Nontrivial := by
  rw [Function.ne_iff]
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨⟨x, hxA, hxB⟩, hne⟩ : Det.some A B ∧ ¬ every A B := by simpa using hB
    obtain ⟨y, hyA, hyB⟩ := Set.not_subset.1 hne
    exact ⟨x, hxA, y, hyA, fun h ↦ hyB (h ▸ hxB)⟩
  · rintro ⟨x, hx, y, hy, hne⟩
    have h : Det.some A {x} ∧ ¬ every A {x} := ⟨⟨x, hx, rfl⟩, fun h ↦ hne (h hy).symm⟩
    exact ⟨{x}, by simpa using h⟩

/-- `every A` and `no A` are contrary, unable both to hold and able both to fail, exactly when
`A` has two members. -/
theorem isContrary_every_no_iff : Aristotelian.IsContrary (every A) (no A) ↔ A.Nontrivial :=
  ⟨fun h ↦ some_inf_compl_every_ne_bot_iff.1 <|
      (squareRelations_square.2 (disjoint_every_no_iff.1 h.disjoint)).isContrary_AE_iff.1 h,
    fun h ↦ (squareRelations_square.2 h.nonempty).isContrary_AE_iff.2 <|
      some_inf_compl_every_ne_bot_iff.2 h⟩

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

theorem satisfiesUniversals_some : (Det.some : Det α).SatisfiesUniversals :=
  satisfiesUniversals_iff.2 ⟨conservative_some, scopeMonotone_some.rightContinuous⟩

theorem satisfiesUniversals_every : (every : Det α).SatisfiesUniversals :=
  satisfiesUniversals_iff.2 ⟨conservative_every, scopeMonotone_every.rightContinuous⟩

theorem satisfiesUniversals_no : (no : Det α).SatisfiesUniversals :=
  satisfiesUniversals_iff.2 ⟨conservative_no, scopeAntitone_no.rightContinuous⟩

end Det

end Quantifier
