module

public import Linglib.Core.ModelTheory.Factor

/-!
# Strictly local and locally testable sets of structures

Among the members of a family of relational structures, a set is strictly `k`-local when a set of
permitted `k`-factors cuts it out, and locally `k`-testable when membership depends only on the
set of `k`-factors. Over words ordered by successor these are the strictly local and the locally
testable stringsets, and over words ordered by precedence the strictly piecewise and the piecewise
testable ones.

## Main definitions

* `FirstOrder.Language.IsStrictlyLocal`, `FirstOrder.Language.IsLocallyTestable`: the strictly
  local and the locally testable sets of members of a family of structures.

## Main statements

* `FirstOrder.Language.isStrictlyLocal_iff`: a set is strictly local exactly when it contains
  every member whose factors all occur in its members.
* `FirstOrder.Language.IsStrictlyLocal.mem_of_factors_subset_union`: strictly local sets are
  closed under any operation that adds no factor.

## References

* [rogers-lambert-2019]
-/

@[expose] public section

universe u v w x

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

variable {M k} {S T : Set ι}

/-! ### Strictly local sets -/

/-- A set is strictly local exactly when it contains every member whose factors all occur in its
members. -/
theorem isStrictlyLocal_iff :
    L.IsStrictlyLocal M k S ↔ ∀ i, L.factors k (M i) ⊆ ⋃ j ∈ S, L.factors k (M j) → i ∈ S := by
  refine ⟨?_, fun h ↦ ⟨⋃ j ∈ S, L.factors k (M j), Set.ext fun i ↦
    ⟨fun hi ↦ Set.subset_biUnion_of_mem (u := fun j ↦ L.factors k (M j)) hi, h i⟩⟩⟩
  rintro ⟨G, rfl⟩ i hi
  exact hi.trans (Set.iUnion₂_subset fun _ hj ↦ hj)

/-- Strictly local sets are closed under any operation that adds no factor. -/
theorem IsStrictlyLocal.mem_of_factors_subset_union (hS : L.IsStrictlyLocal M k S) {a b c : ι}
    (ha : a ∈ S) (hb : b ∈ S) (h : L.factors k (M c) ⊆ L.factors k (M a) ∪ L.factors k (M b)) :
    c ∈ S := by
  obtain ⟨G, rfl⟩ := hS
  exact h.trans (Set.union_subset ha hb)

theorem IsStrictlyLocal.mem_of_factors_subset (hS : L.IsStrictlyLocal M k S) {i j : ι}
    (hi : i ∈ S) (h : L.factors k (M j) ⊆ L.factors k (M i)) : j ∈ S :=
  hS.mem_of_factors_subset_union hi hi (h.trans Set.subset_union_left)

theorem IsStrictlyLocal.comap {κ : Type*} (hS : L.IsStrictlyLocal M k S) (π : κ → ι) :
    L.IsStrictlyLocal (fun j ↦ M (π j)) k (π ⁻¹' S) := by
  obtain ⟨G, rfl⟩ := hS
  exact ⟨G, rfl⟩

theorem IsStrictlyLocal.inter (hS : L.IsStrictlyLocal M k S) (hT : L.IsStrictlyLocal M k T) :
    L.IsStrictlyLocal M k (S ∩ T) := by
  obtain ⟨G, rfl⟩ := hS
  obtain ⟨H, rfl⟩ := hT
  exact ⟨G ∩ H, Set.ext fun _ ↦ Set.subset_inter_iff.symm⟩

/-! ### Locally testable sets -/

theorem IsStrictlyLocal.isLocallyTestable (hS : L.IsStrictlyLocal M k S) :
    L.IsLocallyTestable M k S := by
  obtain ⟨G, rfl⟩ := hS
  exact fun _ _ h ↦ congrArg (· ⊆ G) h

theorem IsLocallyTestable.compl (hS : L.IsLocallyTestable M k S) :
    L.IsLocallyTestable M k Sᶜ :=
  fun _ _ h ↦ congrArg Not (hS h)

theorem IsLocallyTestable.inter (hS : L.IsLocallyTestable M k S)
    (hT : L.IsLocallyTestable M k T) : L.IsLocallyTestable M k (S ∩ T) :=
  fun _ _ h ↦ congrArg₂ And (hS h) (hT h)

theorem IsLocallyTestable.union (hS : L.IsLocallyTestable M k S)
    (hT : L.IsLocallyTestable M k T) : L.IsLocallyTestable M k (S ∪ T) :=
  fun _ _ h ↦ congrArg₂ Or (hS h) (hT h)

end FirstOrder.Language
