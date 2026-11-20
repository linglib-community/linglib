module

public import Linglib.Logic.Truthmaker.Bilateral
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.Order.Concept

/-!
# Exclusion

An exclusion relation `excl` on a state space relates a state to the states it rules out, each
wholly relevant to the other. Two states conflict when a part of one excludes a part of the
other, `Conflict excl s t ↔ ∃ s' ≤ s, ∃ t' ≤ t, excl s' t'`, and a state is possible when it does
not conflict with itself. The possible states form a lower set, `possible excl`. Possible Fusion
holds when two possible states that do not conflict have a possible fusion.

In a complete lattice, a state contains a fusion of one `r`-related state for each member of a
set `P` exactly when it contains an `r`-related state for each member of `P`
(`Truthmaker.mem_upperClosure_setOf_sSup_image`). Negations defined by fusing excluders therefore
have the states that conflict with every verifier as their inexact verifiers.

In the canonical space a literal excludes its mirror image, and the possible states are the
consistent sets of literals (`Truthmaker.Canonical.possible_excl`).

## Implementation notes

Fine takes the possible states as given and constrains exclusion against them. Plebani, Rosella and
Saitta, and Champollion and Bernard, derive them from exclusion, which is what `possible` does.
Fine's conditions on exclusion and his negations are in `Studies/Fine2017a.lean`.

## References

* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
* [M. Plebani, G. Rosella and V. Saitta, *Truthmakers, Incompatibility, and Modality*
  (2022)][plebani-rosella-saitta-2022]
* [L. Champollion and T. Bernard, *Negation and modality in unilateral truthmaker semantics*
  (2024)][champollion-bernard-2024]
-/

@[expose] public section

open SetFamily

namespace Truthmaker

variable {S : Type*}

/-! ### Conflict and possibility -/

section Preorder

variable [Preorder S] {excl : S → S → Prop} {s t : S}

variable (excl) in
/-- Two states conflict when some part of the first excludes some part of the second. -/
def Conflict (s t : S) : Prop :=
  ∃ s' ≤ s, ∃ t' ≤ t, excl s' t'

theorem Conflict.of_excl (h : excl s t) : Conflict excl s t :=
  ⟨s, le_rfl, t, le_rfl, h⟩

theorem Conflict.mono {s' t' : S} (h : Conflict excl s t) (hs : s ≤ s') (ht : t ≤ t') :
    Conflict excl s' t' :=
  let ⟨a, ha, b, hb, hx⟩ := h
  ⟨a, ha.trans hs, b, hb.trans ht, hx⟩

theorem Conflict.symm [Std.Symm excl] (h : Conflict excl s t) : Conflict excl t s :=
  let ⟨a, ha, b, hb, hx⟩ := h
  ⟨b, hb, a, ha, Std.Symm.symm _ _ hx⟩

variable (excl) in
/-- A state is possible when it does not conflict with itself, and every part of a possible state
is possible. -/
def possible : LowerSet S where
  carrier := {s | ¬ Conflict excl s s}
  lower' := by
    intro s t hts hs hc
    exact hs (hc.mono hts hts)

theorem mem_possible : s ∈ possible excl ↔ ¬ Conflict excl s s :=
  Iff.rfl

/-- A state is possible exactly when no two of its parts conflict. -/
theorem mem_possible_iff_forall : s ∈ possible excl ↔ ∀ t ≤ s, ∀ u ≤ s, ¬ Conflict excl t u :=
  ⟨fun hs _ ht _ hu hc ↦ hs (hc.mono ht hu), fun h ↦ h s le_rfl s le_rfl⟩

end Preorder

section SemilatticeSup

variable [SemilatticeSup S] {excl : S → S → Prop} {s t : S}

theorem sup_not_mem_possible (h : excl s t) : s ⊔ t ∉ possible excl :=
  fun hp ↦ hp ((Conflict.of_excl h).mono le_sup_left le_sup_right)

theorem not_conflict_of_sup_mem_possible (h : s ⊔ t ∈ possible excl) : ¬ Conflict excl s t :=
  fun hc ↦ h (hc.mono le_sup_left le_sup_right)

variable (excl) in
/-- Possible Fusion holds when two possible states that do not conflict have a possible
fusion. -/
def PossibleFusion : Prop :=
  ∀ ⦃s : S⦄, s ∈ possible excl → ∀ ⦃t : S⦄, t ∈ possible excl → ¬ Conflict excl s t →
    s ⊔ t ∈ possible excl

theorem possibleFusion_iff : PossibleFusion excl ↔
    ∀ s ∈ possible excl, ∀ t ∈ possible excl, (s ⊔ t ∈ possible excl ↔ ¬ Conflict excl s t) :=
  ⟨fun h _ hs _ ht ↦ ⟨not_conflict_of_sup_mem_possible, fun hc ↦ h hs ht hc⟩,
    fun h _ hs _ ht ↦ (h _ hs _ ht).2⟩

end SemilatticeSup

/-! ### Fusions of related states -/

section CompleteLattice

variable [CompleteLattice S] {r : S → S → Prop} {P : Set S} {x : S}

/-- A state contains a fusion of one `r`-related state for each member of `P` exactly when it
contains an `r`-related state for each member of `P`. -/
theorem mem_upperClosure_setOf_sSup_image :
    x ∈ upperClosure {e | ∃ h : S → S, (∀ p ∈ P, r (h p) p) ∧ sSup (h '' P) = e} ↔
      ∀ p ∈ P, ∃ q ≤ x, r q p := by
  refine ⟨fun hx p hp ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, ⟨h, hh, rfl⟩, hle⟩ := mem_upperClosure.1 hx
    exact ⟨h p, (le_sSup (Set.mem_image_of_mem h hp)).trans hle, hh p hp⟩
  · choose! h hhx hh using h
    exact mem_upperClosure.2 ⟨_, ⟨h, hh, rfl⟩, sSup_le (Set.forall_mem_image.2 hhx)⟩

end CompleteLattice

/-! ### The canonical space -/

namespace Canonical

variable {α : Type*}

/-- In the canonical space a literal excludes its mirror image and nothing else holds. -/
def excl (s t : Set (α × Bool)) : Prop :=
  ∃ x, s = {x} ∧ t = {mirror x}

instance : Std.Symm (excl (α := α)) :=
  ⟨fun _ _ ⟨x, hs, ht⟩ ↦ ⟨mirror x, ht, by rw [hs, mirror_mirror]⟩⟩

theorem conflict_excl_iff {s t : Set (α × Bool)} :
    Conflict excl s t ↔ ∃ x ∈ s, mirror x ∈ t := by
  constructor
  · rintro ⟨_, h₁, _, h₂, x, rfl, rfl⟩
    exact ⟨x, h₁ rfl, h₂ rfl⟩
  · rintro ⟨x, hx₁, hx₂⟩
    exact ⟨{x}, Set.singleton_subset_iff.2 hx₁, _, Set.singleton_subset_iff.2 hx₂, x, rfl, rfl⟩

/-- The states possible under canonical exclusion are the consistent sets of literals. -/
theorem possible_excl : Truthmaker.possible (excl (α := α)) = possible :=
  SetLike.ext fun _ ↦ by
    simp [Truthmaker.mem_possible, conflict_excl_iff, Canonical.mem_possible]

theorem possibleFusion_excl : PossibleFusion (excl (α := α)) := by
  intro s hs t ht hc
  rw [possible_excl] at hs ht ⊢
  rw [conflict_excl_iff] at hc
  rintro x (hx | hx) (hx' | hx')
  · exact hs x hx hx'
  · exact hc ⟨x, hx, hx'⟩
  · exact hc ⟨mirror x, hx', by rwa [mirror_mirror]⟩
  · exact ht x hx hx'

end Canonical

end Truthmaker
