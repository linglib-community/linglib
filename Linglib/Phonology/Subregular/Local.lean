module

public import Linglib.Core.ModelTheory.Factor
public import Linglib.Core.Order.GenerateCompleteBoolean
public import Mathlib.Order.Closure

/-!
# Strictly local and locally testable sets of structures

Fix a family `M : ι → Type*` of structures of a language `L` and a width `k`. A set `S` of members
of the family is *strictly `k`-local* when a set `G` of permitted factors cuts it out,
`S = {i | L.factors k (M i) ⊆ G}`, and *locally `k`-testable* when membership in `S` depends only
on the set `L.factors k (M i)`. For words between their edges ordered by successor, and widths from
two up, these are the strictly local and the locally testable stringsets, and for words ordered by
precedence the strictly piecewise and the piecewise testable ones.

The strictly local sets are the closed sets of a closure operator, which sends a set to the
members all of whose factors occur in its members. They are closed under intersections, and a set
of forbidden factors presents them as well as a set of permitted ones. The locally testable sets
form a Boolean algebra of sets. The factors of one member lie among those of another exactly when
every strictly local set containing the second contains the first, so the locally testable sets
are those generated from the strictly local ones by complements and arbitrary unions, and by the
Boolean operations when the members have finitely many sets of factors among them. Both classes
grow with `k`.

## Main definitions

* `FirstOrder.Language.IsStrictlyLocal`: the strictly local sets of members of a family.
* `FirstOrder.Language.strictlyLocalClosure`: the least strictly local set containing a set, as a
  closure operator.
* `FirstOrder.Language.IsLocallyTestable`: the locally testable sets of members of a family.
* `FirstOrder.Language.locallyTestable`: the locally testable sets, as a Boolean subalgebra.

## Main results

* `FirstOrder.Language.isStrictlyLocal_iff`: a set is strictly local exactly when it contains
  every member whose factors all occur in its members.
* `FirstOrder.Language.isStrictlyLocal_iff_exists_disjoint`: a set is strictly local exactly when
  a set of forbidden factors cuts it out.
* `FirstOrder.Language.IsStrictlyLocal.mem_of_factors_subset_union`: strictly local sets are
  closed under any binary operation that adds no factor.
* `FirstOrder.Language.factors_subset_factors_iff_forall_isStrictlyLocal`: the factors of one
  member lie among those of another exactly when every strictly local set containing the second
  contains the first.
* `FirstOrder.Language.isLocallyTestable_iff_generateCompleteBoolean`: the locally testable sets
  are generated from the strictly local ones by complements and arbitrary unions.
* `FirstOrder.Language.closure_isStrictlyLocal`: when the members have finitely many sets of
  factors among them, the strictly local sets generate the Boolean algebra of locally testable
  sets.
* `FirstOrder.Language.IsStrictlyLocal.mono`, `FirstOrder.Language.IsLocallyTestable.mono`: both
  classes grow with the width.

## Implementation notes

* A class of structures is a set of members of an indexed family, where mathlib's Fraïssé theory
  takes a `Set (CategoryTheory.Bundled L.Structure)`. The classes of the source are relative to
  the intended structures, such as the words between their edges, and the family names those:
  a set of words is then strictly local as it stands, with no closure under isomorphism to carry.
  `IsStrictlyLocal.preimage` pulls a strictly local set back along a map of families.
* Local testability is the condition that membership depends only on the factors. Rogers and
  Lambert call these sets locally definable and define them as the Boolean combinations of strictly
  local sets, over finitely many relation symbols; `closure_isStrictlyLocal` is the agreement of
  the two there. In general the condition defines the closure under complements and arbitrary
  unions instead.
* `strictlyLocalClosure` is built by `ClosureOperator.ofPred`, so that its closed sets are the
  strictly local sets by definition and the lemmas of `ClosureOperator` apply to a hypothesis
  `L.IsStrictlyLocal M k S` as it stands.

## References

* [rogers-lambert-2019]
-/

@[expose] public section

universe u v w x

open Set

namespace FirstOrder.Language

variable {L : Language.{u, v}} {ι : Type x} (M : ι → Type w) [∀ i, L.Structure (M i)] (k : ℕ)

variable (L) in
/-- A set of members of a family of structures is strictly `k`-local when it consists of the
members all of whose `k`-factors a fixed set of factors permits. -/
def IsStrictlyLocal (S : Set ι) : Prop :=
  ∃ G : Set (L.Factor k), S = {i | L.factors k (M i) ⊆ G}

variable (L) in
/-- A set of members of a family of structures is locally `k`-testable when membership depends
only on the set of `k`-factors. -/
def IsLocallyTestable (S : Set ι) : Prop :=
  Function.FactorsThrough (· ∈ S) fun i ↦ L.factors k (M i)

variable {M k} {S T : Set ι} {i j : ι}

/-! ### Strictly local sets -/

@[simp] theorem isStrictlyLocal_setOf_factors_subset (G : Set (L.Factor k)) :
    L.IsStrictlyLocal M k {i | L.factors k (M i) ⊆ G} :=
  ⟨G, rfl⟩

/-- A set is strictly local exactly when a set of forbidden factors cuts it out. -/
theorem isStrictlyLocal_iff_exists_disjoint :
    L.IsStrictlyLocal M k S ↔ ∃ F : Set (L.Factor k), S = {i | Disjoint (L.factors k (M i)) F} :=
  compl_surjective.exists.trans <| exists_congr fun F ↦ by
    simp only [subset_compl_iff_disjoint_right]

variable (L M k) in
/-- The strictly `k`-local closure of a set of members: the members all of whose factors occur in
its members. Its closed sets are the strictly `k`-local sets. -/
@[simps! isClosed]
def strictlyLocalClosure : ClosureOperator (Set ι) :=
  .ofPred (fun S ↦ {i | L.factors k (M i) ⊆ ⋃ j ∈ S, L.factors k (M j)}) (L.IsStrictlyLocal M k)
    (fun _ _ hi ↦ subset_biUnion_of_mem (u := fun j ↦ L.factors k (M j)) hi)
    (fun _ ↦ ⟨_, rfl⟩) <| by
      rintro S _ hS ⟨G, rfl⟩ i hi
      exact hi.trans (iUnion₂_subset hS)

theorem mem_strictlyLocalClosure :
    i ∈ L.strictlyLocalClosure M k S ↔ L.factors k (M i) ⊆ ⋃ j ∈ S, L.factors k (M j) :=
  .rfl

@[simp] theorem subset_strictlyLocalClosure : S ⊆ L.strictlyLocalClosure M k S :=
  (L.strictlyLocalClosure M k).le_closure S

@[simp] theorem isStrictlyLocal_strictlyLocalClosure (S : Set ι) :
    L.IsStrictlyLocal M k (L.strictlyLocalClosure M k S) :=
  (L.strictlyLocalClosure M k).isClosed_closure S

@[simp] theorem strictlyLocalClosure_eq_self :
    L.strictlyLocalClosure M k S = S ↔ L.IsStrictlyLocal M k S :=
  (L.strictlyLocalClosure M k).isClosed_iff.symm

alias ⟨_, IsStrictlyLocal.strictlyLocalClosure_eq⟩ := strictlyLocalClosure_eq_self

theorem strictlyLocalClosure_min (h : S ⊆ T) (hT : L.IsStrictlyLocal M k T) :
    L.strictlyLocalClosure M k S ⊆ T :=
  (L.strictlyLocalClosure M k).closure_min h hT

/-- The closure of a single member consists of the members whose factors occur in it. -/
@[simp] theorem strictlyLocalClosure_singleton (j : ι) :
    L.strictlyLocalClosure M k {j} = {i | L.factors k (M i) ⊆ L.factors k (M j)} :=
  Set.ext fun _ ↦ by rw [mem_strictlyLocalClosure, biUnion_singleton, mem_ofPred_eq]

/-- A set is strictly local exactly when it contains every member whose factors all occur in its
members. -/
theorem isStrictlyLocal_iff :
    L.IsStrictlyLocal M k S ↔ ∀ i, L.factors k (M i) ⊆ ⋃ j ∈ S, L.factors k (M j) → i ∈ S :=
  ClosureOperator.isClosed_iff_closure_le (c := L.strictlyLocalClosure M k)

/-- Strictly local sets are closed under any binary operation that adds no factor. -/
theorem IsStrictlyLocal.mem_of_factors_subset_union (hS : L.IsStrictlyLocal M k S) {a b c : ι}
    (ha : a ∈ S) (hb : b ∈ S) (h : L.factors k (M c) ⊆ L.factors k (M a) ∪ L.factors k (M b)) :
    c ∈ S := by
  obtain ⟨G, rfl⟩ := hS
  exact h.trans (union_subset ha hb)

/-- A strictly local set contains every member whose factors occur in one of its members. -/
theorem IsStrictlyLocal.mem_of_factors_subset (hS : L.IsStrictlyLocal M k S)
    (hi : i ∈ S) (h : L.factors k (M j) ⊆ L.factors k (M i)) : j ∈ S :=
  hS.mem_of_factors_subset_union hi hi (h.trans subset_union_left)

/-- No structure avoids the factor on no variables, so the empty set is strictly local. -/
@[simp] protected theorem IsStrictlyLocal.empty : L.IsStrictlyLocal M k (∅ : Set ι) :=
  ⟨∅, (eq_empty_of_forall_notMem fun i hi ↦ (L.factors_nonempty k (M i)).ne_empty
    (subset_empty_iff.1 hi)).symm⟩

@[simp] theorem strictlyLocalClosure_empty : L.strictlyLocalClosure M k (∅ : Set ι) = ∅ :=
  IsStrictlyLocal.empty.strictlyLocalClosure_eq

@[simp] protected theorem IsStrictlyLocal.univ : L.IsStrictlyLocal M k (univ : Set ι) :=
  (L.strictlyLocalClosure M k).isClosed_top

protected theorem IsStrictlyLocal.sInter {𝒮 : Set (Set ι)}
    (h : ∀ S ∈ 𝒮, L.IsStrictlyLocal M k S) : L.IsStrictlyLocal M k (⋂₀ 𝒮) :=
  ClosureOperator.sInf_isClosed (c := L.strictlyLocalClosure M k) h

protected theorem IsStrictlyLocal.iInter {κ : Sort*} {f : κ → Set ι}
    (h : ∀ a, L.IsStrictlyLocal M k (f a)) : L.IsStrictlyLocal M k (⋂ a, f a) :=
  sInter_range f ▸ .sInter (forall_mem_range.2 h)

protected theorem IsStrictlyLocal.inter (hS : L.IsStrictlyLocal M k S)
    (hT : L.IsStrictlyLocal M k T) : L.IsStrictlyLocal M k (S ∩ T) :=
  sInter_pair S T ▸ .sInter (by simp [hS, hT])

/-- A strictly local set of members of a family is strictly local among the members of any family
mapped into it. -/
theorem IsStrictlyLocal.preimage {κ : Type*} (hS : L.IsStrictlyLocal M k S) (π : κ → ι) :
    L.IsStrictlyLocal (fun a ↦ M (π a)) k (π ⁻¹' S) := by
  obtain ⟨G, rfl⟩ := hS
  exact ⟨G, rfl⟩

/-- A strictly `k`-local set is strictly `k'`-local for `k ≤ k'`. -/
theorem IsStrictlyLocal.mono {k' : ℕ} (hS : L.IsStrictlyLocal M k S) (h : k ≤ k') :
    L.IsStrictlyLocal M k' S := by
  obtain ⟨F, rfl⟩ := isStrictlyLocal_iff_exists_disjoint.1 hS
  exact isStrictlyLocal_iff_exists_disjoint.2 ⟨Factor.castLE h '' F, by
    simp only [disjoint_image_right, preimage_castLE_factors]⟩

/-- The factors of one member lie among those of another exactly when every strictly local set
containing the second contains the first. -/
theorem factors_subset_factors_iff_forall_isStrictlyLocal :
    L.factors k (M i) ⊆ L.factors k (M j) ↔ ∀ S, L.IsStrictlyLocal M k S → j ∈ S → i ∈ S :=
  ⟨fun h _ hS hj ↦ hS.mem_of_factors_subset hj h, fun h ↦
    h _ (isStrictlyLocal_setOf_factors_subset _) (subset_refl (L.factors k (M j)))⟩

/-- Two members have the same factors exactly when no strictly local set separates them. -/
theorem factors_eq_iff_forall_isStrictlyLocal :
    L.factors k (M i) = L.factors k (M j) ↔ ∀ S, L.IsStrictlyLocal M k S → (i ∈ S ↔ j ∈ S) := by
  rw [subset_antisymm_iff, factors_subset_factors_iff_forall_isStrictlyLocal,
    factors_subset_factors_iff_forall_isStrictlyLocal]
  exact ⟨fun h S hS ↦ ⟨h.2 S hS, h.1 S hS⟩, fun h ↦ ⟨fun S hS ↦ (h S hS).2, fun S hS ↦ (h S hS).1⟩⟩

/-! ### Locally testable sets -/

theorem IsStrictlyLocal.isLocallyTestable (hS : L.IsStrictlyLocal M k S) :
    L.IsLocallyTestable M k S := by
  obtain ⟨G, rfl⟩ := hS
  exact fun _ _ h ↦ congrArg (· ⊆ G) h

theorem IsLocallyTestable.mem_iff (hS : L.IsLocallyTestable M k S)
    (h : L.factors k (M i) = L.factors k (M j)) : i ∈ S ↔ j ∈ S :=
  iff_of_eq (hS h)

theorem IsLocallyTestable.preimage_image_eq (hS : L.IsLocallyTestable M k S) :
    (fun i ↦ L.factors k (M i)) ⁻¹' ((fun i ↦ L.factors k (M i)) '' S) = S :=
  subset_antisymm (fun _ ⟨_, hj, e⟩ ↦ (hS.mem_iff e).1 hj) (subset_preimage_image _ _)

/-- A set is locally testable exactly when it is the preimage of a set of sets of factors. -/
theorem isLocallyTestable_iff_exists_preimage :
    L.IsLocallyTestable M k S ↔
      ∃ P : Set (Set (L.Factor k)), S = (fun i ↦ L.factors k (M i)) ⁻¹' P :=
  ⟨fun h ↦ ⟨_, h.preimage_image_eq.symm⟩, by
    rintro ⟨P, rfl⟩ _ _ e
    exact congrArg (· ∈ P) e⟩

@[simp] protected theorem IsLocallyTestable.empty : L.IsLocallyTestable M k (∅ : Set ι) :=
  fun _ _ _ ↦ rfl

@[simp] protected theorem IsLocallyTestable.univ : L.IsLocallyTestable M k (univ : Set ι) :=
  fun _ _ _ ↦ rfl

protected theorem IsLocallyTestable.compl (hS : L.IsLocallyTestable M k S) :
    L.IsLocallyTestable M k Sᶜ :=
  fun _ _ h ↦ congrArg Not (hS h)

@[simp] theorem isLocallyTestable_compl_iff :
    L.IsLocallyTestable M k Sᶜ ↔ L.IsLocallyTestable M k S :=
  ⟨fun h ↦ compl_compl S ▸ h.compl, .compl⟩

protected theorem IsLocallyTestable.inter (hS : L.IsLocallyTestable M k S)
    (hT : L.IsLocallyTestable M k T) : L.IsLocallyTestable M k (S ∩ T) :=
  fun _ _ h ↦ congrArg₂ And (hS h) (hT h)

protected theorem IsLocallyTestable.union (hS : L.IsLocallyTestable M k S)
    (hT : L.IsLocallyTestable M k T) : L.IsLocallyTestable M k (S ∪ T) :=
  fun _ _ h ↦ congrArg₂ Or (hS h) (hT h)

protected theorem IsLocallyTestable.iUnion {κ : Sort*} {f : κ → Set ι}
    (h : ∀ a, L.IsLocallyTestable M k (f a)) : L.IsLocallyTestable M k (⋃ a, f a) :=
  fun _ _ e ↦ propext <| by
    simp only [mem_iUnion]
    exact exists_congr fun a ↦ (h a).mem_iff e

protected theorem IsLocallyTestable.iInter {κ : Sort*} {f : κ → Set ι}
    (h : ∀ a, L.IsLocallyTestable M k (f a)) : L.IsLocallyTestable M k (⋂ a, f a) :=
  fun _ _ e ↦ propext <| by
    simp only [mem_iInter]
    exact forall_congr' fun a ↦ (h a).mem_iff e

/-- A locally testable set of members of a family is locally testable among the members of any
family mapped into it. -/
theorem IsLocallyTestable.preimage {κ : Type*} (hS : L.IsLocallyTestable M k S) (π : κ → ι) :
    L.IsLocallyTestable (fun a ↦ M (π a)) k (π ⁻¹' S) :=
  fun _ _ h ↦ hS h

/-- A locally `k`-testable set is locally `k'`-testable for `k ≤ k'`. -/
theorem IsLocallyTestable.mono {k' : ℕ} (hS : L.IsLocallyTestable M k S) (h : k ≤ k') :
    L.IsLocallyTestable M k' S :=
  fun i j e ↦ hS (a := i) (b := j) <| by
    simpa only [preimage_castLE_factors] using congrArg (Factor.castLE h ⁻¹' ·) e

variable (L M k) in
/-- The locally `k`-testable sets of members of a family, as a Boolean subalgebra. -/
def locallyTestable : BooleanSubalgebra (Set ι) where
  carrier := {S | L.IsLocallyTestable M k S}
  supClosed' _ hS _ hT := hS.union hT
  infClosed' _ hS _ hT := hS.inter hT
  compl_mem' hS := hS.compl
  bot_mem' := .empty

@[simp] theorem mem_locallyTestable :
    S ∈ L.locallyTestable M k ↔ L.IsLocallyTestable M k S :=
  .rfl

/-- The locally testable sets are those generated from the strictly local sets by complements and
arbitrary unions. -/
theorem isLocallyTestable_iff_generateCompleteBoolean :
    L.IsLocallyTestable M k S ↔ GenerateCompleteBoolean {T | L.IsStrictlyLocal M k T} S :=
  Iff.trans
    ⟨fun h _ _ e ↦ h <| factors_eq_iff_forall_isStrictlyLocal.2 fun T hT ↦
        iff_of_eq (congrFun e ⟨T, hT⟩),
      fun h _ _ e ↦ h <| funext fun T ↦
        propext (factors_eq_iff_forall_isStrictlyLocal.1 e T T.2)⟩
    (generateCompleteBoolean_iff_factorsThrough (OrderIso.refl (Set ι))).symm

/-- A Boolean combination of strictly local sets is locally testable. -/
theorem closure_isStrictlyLocal_le :
    BooleanSubalgebra.closure {S | L.IsStrictlyLocal M k S} ≤ L.locallyTestable M k :=
  BooleanSubalgebra.closure_le.2 fun _ ↦ IsStrictlyLocal.isLocallyTestable

/-- When the members have finitely many sets of factors among them, there are finitely many
strictly local sets. -/
theorem finite_setOf_isStrictlyLocal (h : (range fun i ↦ L.factors k (M i)).Finite) :
    {S | L.IsStrictlyLocal M k S}.Finite :=
  (h.finite_subsets.image ((fun i ↦ L.factors k (M i)) ⁻¹' ·)).subset fun _ hS ↦
    ⟨_, image_subset_range _ _, hS.isLocallyTestable.preimage_image_eq⟩

/-- When the members have finitely many sets of factors among them, the strictly local sets
generate the Boolean algebra of the locally testable sets. -/
theorem closure_isStrictlyLocal (h : (range fun i ↦ L.factors k (M i)).Finite) :
    BooleanSubalgebra.closure {S | L.IsStrictlyLocal M k S} = L.locallyTestable M k :=
  BooleanSubalgebra.ext fun S ↦ by
    rw [mem_locallyTestable, isLocallyTestable_iff_generateCompleteBoolean,
      generateCompleteBoolean_iff_mem_closure (finite_setOf_isStrictlyLocal h)]

/-- With finitely many `k`-factors, a set is locally testable exactly when it is a Boolean
combination of strictly local sets. -/
theorem isLocallyTestable_iff_mem_closure [Finite (L.Factor k)] :
    L.IsLocallyTestable M k S ↔ S ∈ BooleanSubalgebra.closure {T | L.IsStrictlyLocal M k T} := by
  rw [closure_isStrictlyLocal (toFinite _), mem_locallyTestable]

end FirstOrder.Language
