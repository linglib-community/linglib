module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic

/-!
# Antimatroids

Antimatroids are combinatorial structures that generalize the notion of a partial
order. They were first described by [dilworth-1940] in the context of lattice
theory and have been rediscovered many times under different names
([monjardet-1985]; see [korte-lovasz-schrader-1991] for a comprehensive survey).
An antimatroid is uniquely determined by its *rooted circuits* ([dietrich-1987]).

This file develops the framework-agnostic theory; the Optimality-Theory
specialization (the ERC–antimatroid isomorphism of [merchant-riggle-2016]) lives
in `Linglib.Phonology.OptimalityTheory.Antimatroid`.

**[UPSTREAM]**: mathlib has `Matroid` but no `Antimatroid`/`Greedoid`. The design
mirrors mathlib's `Matroid`: a bundled structure (not a typeclass) with a `Set α`
ground set and `Prop` axioms.

## Main definitions

* `SetSystem` — a ground set `E` with a collection of feasible subsets.
* `AccessibleSetSystem` — a set system with augmentation and removal.
* `Antimatroid` — an accessible set system closed under union.
* `Antimatroid.Finite` — finiteness of the ground set, as an inferable class.
* `Antimatroid.free` — the free antimatroid on `E` (every subset feasible).
* `Antimatroid.trace` — the trace `A : S`, restricting feasibility to `· ∩ S`.
* `Antimatroid.RootedCircuit` — a minimal non-free trace, with a root.

## References

[dilworth-1940] — Lattices with unique irreducible decompositions
[monjardet-1985] — A use for frequently rediscovering a concept (antimatroids)
[dietrich-1987] — A circuit set characterization of antimatroids
[korte-lovasz-schrader-1991] — Greedoids
[merchant-riggle-2016] — OT grammars, beyond partial orders: ERC sets and antimatroids
-/

@[expose] public section

/-! ### Set systems -/

/-- A **set system** `(G, F)` is a finite ground set `G` with a
    collection `F` of subsets of `G`, called **feasible sets**.

    Any subset of a power set is a set system. The feasible sets are
    the subsets of `G` that the system "recognizes." -/
structure SetSystem (α : Type*) where
  /-- The ground set. -/
  E : Set α
  /-- The feasible set predicate: `IsFeasible S` means `S` is a
      recognized subset of the ground set. -/
  IsFeasible : Set α → Prop
  /-- The empty set is always feasible. -/
  empty_feasible : IsFeasible ∅
  /-- Feasible sets are subsets of the ground set. -/
  feasible_sub : ∀ S, IsFeasible S → S ⊆ E

/-! ### Accessible set systems -/

/-- An **accessible set system** is a set system with augmentation and
    removal properties. Informally:

    - **Augmentation**: any feasible set that isn't the full ground set
      can be extended by adding one element to produce another feasible set.
    - **Removal**: any non-empty feasible set can be shrunk by removing
      one element to produce another feasible set.

    The term "accessible" refers to the fact that both the empty set and
    the ground set are reachable from any feasible set via single-element
    additions or removals.

    [merchant-riggle-2016] Definition 3. -/
structure AccessibleSetSystem (α : Type*) extends SetSystem α where
  /-- The ground set is feasible. -/
  ground_feasible : IsFeasible E
  /-- Every feasible set other than the ground set extends by an element of the ground set to
      a feasible set. -/
  augmentation : ∀ S, IsFeasible S → S ≠ E →
    ∃ x ∈ E, x ∉ S ∧ IsFeasible (insert x S)
  /-- Every nonempty feasible set shrinks by one of its elements to a feasible set. -/
  removal : ∀ S, IsFeasible S → S.Nonempty →
    ∃ x ∈ S, IsFeasible (S \ {x})

/-! ### Antimatroids -/

/-- An **antimatroid** is an accessible set system that is closed under
    union: the union of any two feasible sets is also feasible.

    The three defining properties — accessibility (augmentation + removal)
    and union closure — are what [merchant-riggle-2016] prove isomorphic to
    consistent ERC sets.

    The design follows mathlib's `Matroid`: bundled structure (not a
    typeclass), `Set α` ground set, `Prop` axioms.

    [merchant-riggle-2016] Definition 5. -/
structure Antimatroid (α : Type*) extends AccessibleSetSystem α where
  /-- The union of two feasible sets is feasible, which distinguishes antimatroids among
      accessible set systems. -/
  union_closed : ∀ S T, IsFeasible S → IsFeasible T → IsFeasible (S ∪ T)

/-! ### Finiteness -/

/-- An antimatroid with a finite ground set. Following mathlib's
    `Matroid.Finite`, this is a typeclass so it can be inferred. -/
class Antimatroid.Finite {α : Type*} (A : Antimatroid α) : Prop where
  ground_finite : A.E.Finite

theorem Antimatroid.ground_finite {α : Type*} (A : Antimatroid α)
    [A.Finite] : A.E.Finite :=
  Antimatroid.Finite.ground_finite

/-! ### Basic properties -/

variable {α : Type*}

@[ext] theorem Antimatroid.ext {A B : Antimatroid α} (hE : A.E = B.E)
    (hF : A.IsFeasible = B.IsFeasible) : A = B := by
  obtain ⟨⟨⟨E, F, _, _⟩, _, _, _⟩, _⟩ := A
  obtain ⟨⟨⟨E', F', _, _⟩, _, _, _⟩, _⟩ := B
  cases hE; cases hF; rfl

theorem Antimatroid.ground_isFeasible (A : Antimatroid α) :
    A.IsFeasible A.E :=
  A.ground_feasible

theorem Antimatroid.empty_isFeasible (A : Antimatroid α) :
    A.IsFeasible ∅ :=
  A.empty_feasible

/-- Singletons in the ground set are feasible in any antimatroid.

    Proof: the empty set is feasible and not equal to `E` (since `E`
    contains `x`), so by augmentation there exists some `y ∈ E` with
    `{y}` feasible. By induction (via removal from larger sets), every
    singleton is feasible.

    For now, we prove only the weaker statement that some singleton
    exists. -/
theorem Antimatroid.exists_singleton_feasible (A : Antimatroid α)
    (hne : A.E.Nonempty) : ∃ x ∈ A.E, A.IsFeasible {x} := by
  have hne_ground : (∅ : Set α) ≠ A.E := by
    intro h; obtain ⟨x, hx⟩ := hne; simp [← h] at hx
  obtain ⟨x, hx_mem, _, hx_feas⟩ := A.augmentation ∅ A.empty_feasible hne_ground
  have : insert x (∅ : Set α) = {x} := by ext; simp
  rw [this] at hx_feas
  exact ⟨x, hx_mem, hx_feas⟩

/-! ### The free antimatroid -/

/-- The **free antimatroid** on a set `E`: every subset is feasible.

    This corresponds to the OT system with no ranking requirements
    (the empty ERC set) — all `n!` rankings are consistent.
    [merchant-riggle-2016] Definition 8. -/
def Antimatroid.free (E : Set α) : Antimatroid α where
  E := E
  IsFeasible := fun S => S ⊆ E
  empty_feasible := Set.empty_subset E
  feasible_sub := fun _ h => h
  ground_feasible := Set.Subset.refl E
  augmentation := fun S hS hne => by
    obtain ⟨x, hxE, hxS⟩ : ∃ x, x ∈ E ∧ x ∉ S := by
      by_contra h
      apply hne
      ext x
      constructor
      · intro hx; exact hS hx
      · intro hx
        by_contra hxS
        exact h ⟨x, hx, hxS⟩
    exact ⟨x, hxE, hxS, Set.insert_subset hxE hS⟩
  removal := fun S hS hne => by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, Set.sdiff_subset.trans hS⟩
  union_closed := fun _ _ hS hT => Set.union_subset hS hT

theorem Antimatroid.free_isFeasible (E : Set α) (S : Set α) :
    (Antimatroid.free E).IsFeasible S ↔ S ⊆ E :=
  Iff.rfl

/-! ### Traces -/

/-- The **trace** of antimatroid `A` on subset `S ⊆ E` is the
    antimatroid `(S, {f ∩ S | f ∈ F})` — restricting the feasible
    sets to their intersections with `S`.

    Traces capture the ordering relations that the original antimatroid
    places on the constraints in `S`.

    [merchant-riggle-2016] Definition 7. -/
def Antimatroid.trace (A : Antimatroid α) (S : Set α) (_hS : S ⊆ A.E) :
    SetSystem α where
  E := S
  IsFeasible := fun T => ∃ F, A.IsFeasible F ∧ T = F ∩ S
  empty_feasible := ⟨∅, A.empty_feasible, by simp⟩
  feasible_sub := fun T ⟨F, _, hT⟩ => hT ▸ Set.inter_subset_right

/-! ### Rooted circuits -/

/-- A **rooted circuit** of antimatroid `A` on `S ⊆ E` is a trace
    `A : S` such that every proper subset of `S` gives a free trace
    (no ordering constraints), but `A : S` itself is not free.

    Rooted circuits are the minimal subsets of `E` that encode actual
    ranking requirements. Each rooted circuit corresponds to exactly
    one ERC under `OptimalityTheory.ERC.ofRootedCircuit`.

    The **root** of the circuit is the unique element `r ∈ S` such that
    `{r}` is not feasible in `A : S`.

    [merchant-riggle-2016] Definition 9. -/
structure Antimatroid.RootedCircuit (A : Antimatroid α) where
  /-- The set defining the circuit. -/
  carrier : Set α
  /-- The carrier is a subset of the ground set. -/
  carrier_sub : carrier ⊆ A.E
  /-- The root element. -/
  root : α
  /-- The root is in the carrier. -/
  root_mem : root ∈ carrier
  /-- The trace on the carrier is not free: `{root}` is not feasible
      in the trace. -/
  not_free : ¬ (A.trace carrier carrier_sub).IsFeasible {root}
  /-- Every proper subset of the carrier gives a free trace:
      for every `T ⊂ carrier` and `x ∈ T`, the singleton `{x}` is
      feasible in the trace `A : T`. -/
  proper_free : ∀ T : Set α, ∀ hT : T ⊂ carrier,
    ∀ x ∈ T,
      (A.trace T (hT.subset.trans carrier_sub)).IsFeasible {x}

/-! ### Rooted-circuit extraction ([dietrich-1987]) -/

theorem Antimatroid.exists_insert_step (A : Antimatroid α) {G : Set α}
    (hfin : G.Finite) (hG : A.IsFeasible G) {x : α} (hx : x ∈ G) :
    ∃ H, A.IsFeasible H ∧ H ⊆ G ∧ x ∉ H ∧ A.IsFeasible (insert x H) := by
  induction hcard : G.ncard using Nat.strong_induction_on generalizing G with
  | _ m ih =>
    obtain ⟨z, hz, hz_feas⟩ := A.removal G hG ⟨x, hx⟩
    rcases eq_or_ne z x with rfl | hzx
    · refine ⟨G \ {z}, hz_feas, Set.sdiff_subset, by simp, ?_⟩
      rwa [Set.insert_sdiff_singleton, Set.insert_eq_self.mpr hz]
    · obtain ⟨H, h1, h2, h3, h4⟩ := ih _
        (hcard ▸ Set.ncard_sdiff_singleton_lt_of_mem hz hfin)
        (hfin.subset Set.sdiff_subset) hz_feas ⟨hx, hzx.symm⟩ rfl
      exact ⟨H, h1, h2.trans Set.sdiff_subset, h3, h4⟩

/-- If no feasible set meets `W` exactly in `{x}`, some circuit rooted at `x` lies inside `W`
([merchant-riggle-2016] Lemma 8, after [dietrich-1987]). -/
theorem Antimatroid.exists_rootedCircuit_of_critical (A : Antimatroid α)
    (hfin : A.E.Finite) {W : Set α} (hWE : W ⊆ A.E) {x : α} (hxW : x ∈ W)
    (hcrit : ¬∃ F, A.IsFeasible F ∧ F ∩ W = {x}) :
    ∃ rc : A.RootedCircuit, rc.root = x ∧ rc.carrier ⊆ W := by
  classical
  set crit : Set α → Prop :=
    fun D => x ∈ D ∧ D ⊆ W ∧ ¬∃ F, A.IsFeasible F ∧ F ∩ D = {x} with hcrit_def
  have hW : crit W := ⟨hxW, le_refl _, hcrit⟩
  -- a cardinality-minimal critical set
  have hex : ∃ m : ℕ, ∃ D, crit D ∧ D.ncard = m := ⟨W.ncard, W, hW, rfl⟩
  obtain ⟨C, hC, hCcard⟩ := Nat.find_spec hex
  have hmin : ∀ D, crit D → C.ncard ≤ D.ncard := fun D hD =>
    hCcard ▸ Nat.find_min' hex ⟨D, hD, rfl⟩
  obtain ⟨hxC, hCW, hCcrit⟩ := hC
  have hCfin : C.Finite := (hfin.subset hWE).subset hCW
  -- near-critical subsets provide two-point intersections
  have hpair : ∀ w ∈ C, w ≠ x → ∃ F, A.IsFeasible F ∧ F ∩ C = {x, w} := by
    intro w hw hwx
    have hnotcrit : ¬crit (C \ {w}) := fun h =>
      absurd (hmin _ h) (Nat.not_le.mpr (Set.ncard_sdiff_singleton_lt_of_mem hw hCfin))
    simp only [hcrit_def, not_and, not_not] at hnotcrit
    obtain ⟨F, hF, hFC⟩ := hnotcrit ⟨hxC, hwx.symm⟩ (Set.sdiff_subset.trans hCW)
    have hxF : x ∈ F := (hFC.symm.subset rfl).1
    have hwF : w ∈ F := by
      by_contra hwF
      refine hCcrit ⟨F, hF, ?_⟩
      rw [← hFC]
      ext y
      simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, fun hy => hwF (hy ▸ h1)⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩
    refine ⟨F, hF, ?_⟩
    ext y
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨hyF, hyC⟩
      by_contra hy
      push Not at hy
      have hmem : y ∈ F ∩ (C \ {w}) := ⟨hyF, hyC, hy.2⟩
      rw [hFC] at hmem
      exact hy.1 hmem
    · rintro (rfl | rfl)
      exacts [⟨hxF, hxC⟩, ⟨hwF, hw⟩]
  -- assemble the rooted circuit
  refine ⟨⟨C, hCW.trans hWE, x, hxC, ?_, ?_⟩, rfl, hCW⟩
  · rintro ⟨F, hF, hFC⟩
    exact hCcrit ⟨F, hF, hFC.symm⟩
  · intro T hT y hy
    have hTC : T ⊆ C := hT.subset
    rcases eq_or_ne y x with rfl | hyx
    · have hnotcrit : ¬crit T := fun h =>
        absurd (hmin _ h) (Nat.not_le.mpr (Set.ncard_lt_ncard hT hCfin))
      simp only [hcrit_def, not_and, not_not] at hnotcrit
      obtain ⟨F, hF, hFT⟩ := hnotcrit hy (hTC.trans hCW)
      exact ⟨F, hF, hFT.symm⟩
    · obtain ⟨G, hG, hGC⟩ := hpair y (hTC hy) hyx
      have hyG : y ∈ G := (hGC.symm.subset (Or.inr rfl)).1
      by_cases hxT : x ∈ T
      · -- split G at the first appearance of x
        obtain ⟨H, hH, hHG, hxH, hxHfeas⟩ :=
          A.exists_insert_step (hfin.subset (A.feasible_sub G hG)) hG
            ((hGC.symm.subset (Or.inl rfl)).1)
        by_cases hyH : y ∈ H
        · refine ⟨H, hH, ?_⟩
          ext z
          simp only [Set.mem_singleton_iff, Set.mem_inter_iff]
          constructor
          · rintro rfl; exact ⟨hyH, hy⟩
          · intro ⟨hzH, hzT⟩
            have : z ∈ G ∩ C := ⟨hHG hzH, hTC hzT⟩
            rw [hGC] at this
            rcases this with rfl | rfl
            · exact absurd hzH hxH
            · rfl
        · exfalso
          refine hCcrit ⟨insert x H, hxHfeas, ?_⟩
          ext z
          simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · intro ⟨hz, hzC⟩
            rcases hz with rfl | hzH
            · rfl
            · have : z ∈ G ∩ C := ⟨hHG hzH, hzC⟩
              rw [hGC] at this
              rcases this with rfl | rfl
              exacts [rfl, absurd hzH hyH]
          · rintro rfl; exact ⟨Or.inl rfl, hxC⟩
      · refine ⟨G, hG, ?_⟩
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_inter_iff]
        constructor
        · rintro rfl; exact ⟨hyG, hy⟩
        · intro ⟨hzG, hzT⟩
          have : z ∈ G ∩ C := ⟨hzG, hTC hzT⟩
          rw [hGC] at this
          rcases this with rfl | rfl
          exacts [absurd hzT hxT, rfl]
