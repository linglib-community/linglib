module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Multiset.Bind

/-!
# Fission

Fission lets one syntactic node be realized in several adjacent positions of exponence. A
Vocabulary Item inserted at the node discharges only the features it spells out, and the remaining
features fission off to a subsidiary position where insertion continues. Here this is the strict
scansion of González Poot and McGinnis: the Vocabulary is scanned once, top to bottom, and an item
is inserted when one of the node's matrices bears every feature of its site, discharging those
features from that matrix; scansion halts at the bottom of the list, so no item is inserted twice.
Halle's Fission instead repeats insertion on the subsidiary morpheme.

An item's features and a matrix are finite sets, and a node bears several matrices, one per
argument it agrees with, as the Yucatec Agr3 agrees with both subject and object; an item draws on
one of them. A feature borne by two of a node's matrices is borne twice, so the theorems are stated
in the free commutative monoid `Multiset F`, where the node is the sum of its matrices, discharge
is set difference, and scansion is a greedy decomposition of the node.

## Main definitions

* `discharge`: remove the features an item spells out from the first matrix bearing them all.
* `scan`, `insertions`, `residue`, `scansion`: the items a node's matrices receive under strict
  scansion with local Fission, the matrices left over, and the items' exponents.

## Main results

* `bind_insertions_add_residue`: in the free commutative monoid on the features, the inserted
  items' features and the residue sum to the node.
* `bind_insertions_le`, `pairwise_disjoint_insertions`: the inserted items' features fit inside the
  node, and on a node whose matrices are disjoint they are disjoint.
* `head?_insertions_singleton`, `head?_scansion_singleton`: at a single matrix the first insertion
  is the first applicable item, so on a Vocabulary ordered by specificity it is the Subset
  Principle's winner.

## References

* [R. Noyer, *Features, positions and affixes in autonomous morphological
  structure*][noyer-1992]
* [M. Halle, *Distributed Morphology: Impoverishment and Fission*][halle-1997]
* [A. González Poot and M. McGinnis, *Local versus long-distance Fission in
  Distributed Morphology*][gonzalez-poot-mcginnis-2006]
-/

@[expose] public section

namespace DistributedMorphology

open Morphology.Exponence

variable {F E : Type*} [DecidableEq F]

/-- Discharging an item removes the features it spells out from the first of the matrices bearing
them all, in the environment `env` (whose focus is ignored), and fails when no matrix does. -/
def discharge (i : VocabularyItem F E) (env : Neighborhood (Finset F)) :
    List (Finset F) → Option (List (Finset F))
  | [] => none
  | m :: ms =>
    if Applies i ({ env with focus := m } : Neighborhood (Finset F)) then
      some (m \ i.features :: ms)
    else (discharge i env ms).map (m :: ·)

/-- Strict scansion with local Fission at a node bearing the matrices `ms` in the environment
`env` yields the items inserted, in Vocabulary order, and the matrices left over. -/
def scan : RuleSet (VocabularyItem F E) → Neighborhood (Finset F) → List (Finset F) →
    List (VocabularyItem F E) × List (Finset F)
  | [], _, ms => ([], ms)
  | i :: rest, env, ms =>
    match discharge i env ms with
    | some ms' => (scan rest env ms').map (i :: ·) id
    | none => scan rest env ms

/-- `insertions` lists the items scansion inserts. -/
def insertions (items : RuleSet (VocabularyItem F E)) (env : Neighborhood (Finset F))
    (ms : List (Finset F)) : List (VocabularyItem F E) :=
  (scan items env ms).1

/-- `residue` lists the matrices scansion leaves, the features no inserted item discharged. -/
def residue (items : RuleSet (VocabularyItem F E)) (env : Neighborhood (Finset F))
    (ms : List (Finset F)) : List (Finset F) :=
  (scan items env ms).2

/-- A node bearing the matrices `ms` in the environment `env` receives these exponents. -/
def scansion (items : RuleSet (VocabularyItem F E)) (env : Neighborhood (Finset F))
    (ms : List (Finset F)) : List E :=
  (insertions items env ms).map (·.exponent)

variable {items rest : RuleSet (VocabularyItem F E)} {env : Neighborhood (Finset F)}
  {i : VocabularyItem F E} {ms ms' : List (Finset F)}

@[simp] theorem discharge_nil (i : VocabularyItem F E) : discharge i env [] = none := rfl

@[simp] theorem scan_nil (env : Neighborhood (Finset F)) (ms : List (Finset F)) :
    scan ([] : RuleSet (VocabularyItem F E)) env ms = ([], ms) := rfl

theorem scan_cons_of_discharge_eq_some (h : discharge i env ms = some ms') :
    scan (i :: rest) env ms = (i :: insertions rest env ms', residue rest env ms') := by
  simp only [scan, h]; rfl

theorem scan_cons_of_discharge_eq_none (h : discharge i env ms = none) :
    scan (i :: rest) env ms = scan rest env ms := by
  simp [scan, h]

/-- Discharge subtracts the item's features from the node, the sum of its matrices. -/
theorem val_add_discharge : ∀ {ms ms' : List (Finset F)}, discharge i env ms = some ms' →
    i.features.val + (ms'.map Finset.val).sum = (ms.map Finset.val).sum
  | [], _, h => by simp at h
  | m :: ms, ms', h => by
    unfold discharge at h
    split_ifs at h with hs
    · cases h
      have hle : i.features ⊆ m := fun f hf ↦ by
        simpa [Neighborhood.mem_def] using hs _ (VocabularyItem.mem_features.1 hf)
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, Finset.sdiff_val,
        ← add_assoc, add_tsub_cancel_of_le (Finset.val_le_iff.2 hle)]
    · obtain ⟨ms'', h'', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, add_left_comm,
        val_add_discharge h'']

/-- **Conservation.** In the free commutative monoid on the features, the inserted items'
features and the residue sum to the node. -/
theorem bind_insertions_add_residue :
    ∀ (items : RuleSet (VocabularyItem F E)) (ms : List (Finset F)),
    (insertions items env ms : Multiset (VocabularyItem F E)).bind (·.features.val) +
      ((residue items env ms).map Finset.val).sum = (ms.map Finset.val).sum
  | [], _ => by simp [insertions, residue]
  | i :: rest, ms => by
    cases h : discharge i env ms with
    | none =>
      simpa [insertions, residue, scan_cons_of_discharge_eq_none h] using
        bind_insertions_add_residue rest ms
    | some ms' =>
      rw [insertions, residue, scan_cons_of_discharge_eq_some h]
      dsimp only
      rw [← Multiset.cons_coe, Multiset.cons_bind, add_assoc,
        bind_insertions_add_residue rest ms', val_add_discharge h]

/-- **No multiple exponence.** The inserted items' features fit inside the node, so no feature is
discharged more often than the node bears it. -/
theorem bind_insertions_le (items : RuleSet (VocabularyItem F E)) (ms : List (Finset F)) :
    (insertions items env ms : Multiset (VocabularyItem F E)).bind (·.features.val) ≤
      (ms.map Finset.val).sum :=
  bind_insertions_add_residue items ms ▸ Multiset.le_add_right _ _

/-- On a node whose matrices are disjoint the inserted items' features are disjoint, so the items
partition the features they discharge. -/
theorem pairwise_disjoint_insertions (h : (ms.map Finset.val).sum.Nodup) :
    (insertions items env ms).Pairwise fun i j ↦ Disjoint i.features j.features := by
  have := Multiset.nodup_of_le (bind_insertions_le (env := env) items ms) h
  rw [Multiset.nodup_bind, Multiset.pairwise_coe_iff_pairwise] at this
  exact this.2.imp (Finset.disjoint_val.mp ·)

/-- A node with no matrix receives nothing. -/
@[simp] theorem insertions_nil_right :
    ∀ items : RuleSet (VocabularyItem F E), insertions items env [] = []
  | [] => rfl
  | _ :: rest => insertions_nil_right rest

@[simp] theorem scansion_nil : scansion items env [] = [] := by simp [scansion]

/-- Each item is inserted at most once, in Vocabulary order. -/
theorem insertions_sublist : ∀ (items : RuleSet (VocabularyItem F E)) (ms : List (Finset F)),
    (insertions items env ms).Sublist items
  | [], _ => .slnil
  | i :: rest, ms => by
    cases h : discharge i env ms with
    | none =>
      rw [insertions, scan_cons_of_discharge_eq_none h]
      exact (insertions_sublist rest ms).cons _
    | some ms' =>
      rw [insertions, scan_cons_of_discharge_eq_some h]
      exact (insertions_sublist rest ms').cons_cons _

theorem scansion_sublist (ms : List (Finset F)) :
    (scansion items env ms).Sublist (items.map (·.exponent)) :=
  (insertions_sublist items ms).map _

theorem length_scansion_le (ms : List (Finset F)) :
    (scansion items env ms).length ≤ items.length := by
  simpa using (scansion_sublist (items := items) (env := env) ms).length_le

/-- At a single matrix, an item discharges iff it applies there. -/
theorem discharge_singleton (i : VocabularyItem F E) (m : Finset F) :
    discharge i env [m] =
      if Applies i ({ env with focus := m } : Neighborhood (Finset F))
        then some [m \ i.features] else none := by
  simp [discharge]

/-- At a single matrix, the first item inserted is the first item that applies there. -/
theorem head?_insertions_singleton (m : Finset F) : ∀ items : RuleSet (VocabularyItem F E),
    (insertions items env [m]).head? =
      (items.applicable ({ env with focus := m } : Neighborhood (Finset F))).head?
  | [] => rfl
  | i :: rest => by
    by_cases h : Applies i ({ env with focus := m } : Neighborhood (Finset F))
    · rw [insertions, scan_cons_of_discharge_eq_some (by rw [discharge_singleton, ite_eq_left h])]
      simp [RuleSet.applicable, h]
    · rw [insertions, scan_cons_of_discharge_eq_none (by rw [discharge_singleton, ite_eq_right h])]
      simpa [insertions, RuleSet.applicable, h] using
        head?_insertions_singleton m rest

/-- On a Vocabulary ordered by decreasing specificity, the first insertion at a single matrix is
the Subset Principle's winner, so scansion agrees with Elsewhere competition where both
apply. -/
theorem head?_scansion_singleton (m : Finset F)
    (hsorted : items.Pairwise fun i j => j.specificity ≤ i.specificity) :
    (scansion items env [m]).head? =
      (winner? items ({ env with focus := m } : Neighborhood (Finset F))).map (·.exponent) := by
  rw [scansion, List.head?_map, head?_insertions_singleton, winner?,
    RuleSet.selectBy_eq_head? hsorted]

end DistributedMorphology
