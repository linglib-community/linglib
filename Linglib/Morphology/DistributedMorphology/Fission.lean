module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.AddSub

/-!
# Fission

Fission lets one syntactic node be realized in several adjacent positions of exponence. A
Vocabulary Item inserted at the node discharges only the features it spells out, and the remaining
features fission off to a subsidiary position where insertion continues. Here this is strict
scansion: the Vocabulary is scanned once, top to bottom, and an item is inserted when one of the
node's matrices bears every feature of its site, discharging one occurrence of each; scansion halts
at the bottom of the list, so no item is inserted twice.

An item's features are a finite set, while a matrix is a multiset, so that a feature borne twice
is two repetitions in Marcolli, Chomsky and Berwick's sense and two items may discharge it one at a
time. A list represents a matrix for computation, and the theorems are stated in the free
commutative monoid `Multiset F`, where discharge is truncated subtraction and scansion a greedy
decomposition of the node. A node may
bear several matrices, one per argument it agrees with, as the Yucatec Agr3 agrees with both
subject and object, and an item draws on one of them.

## Main definitions

* `discharge`: remove one occurrence of each feature an item spells out from the first matrix
  bearing them all.
* `scan`, `insertions`, `residue`, `scansion`: the items a node's matrices receive under strict
  scansion with local Fission, the matrices left over, and the items' exponents.

## Main results

* `bind_insertions_add_residue`: in the free commutative monoid on the features, the inserted
  items' sites and the residue sum to the node.
* `bind_insertions_le`, `pairwise_disjoint_insertions`: the inserted items' sites fit inside the
  node, and on a node without repetitions they are disjoint.
* `head?_insertions_singleton`, `head?_scansion_singleton`: at a single matrix the first insertion
  is the first applicable item, so on a Vocabulary ordered by specificity it is the Subset
  Principle's winner.

## References

* [R. Noyer, *Features, positions and affixes in autonomous morphological
  structure*][noyer-1992]
* [M. Halle, *Distributed Morphology: Impoverishment and Fission*][halle-1997]
* [A. González Poot and M. McGinnis, *Local versus long-distance Fission in
  Distributed Morphology*][gonzalez-poot-mcginnis-2006]
* [M. Marcolli, N. Chomsky and R. C. Berwick, *Mathematical Structure of Syntactic
  Merge*][marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace DistributedMorphology

open Morphology.Exponence

variable {F E : Type*} [DecidableEq F]

/-- `subFeatures m s` removes one occurrence of each element of the multiset `s` from the list
`m`, which does not depend on the order in which `s` is listed. -/
def subFeatures (m : List F) (s : Multiset F) : List F :=
  Quot.liftOn s m.diff fun _ _ h ↦ List.Perm.diff_left m h

@[simp] theorem coe_subFeatures (m : List F) (s : Multiset F) :
    (subFeatures m s : Multiset F) = m - s :=
  Quot.induction_on s fun _ ↦ (Multiset.coe_sub _ _).symm

/-- Discharging an item removes one occurrence of each feature it spells out from the first of
the matrices bearing them all, in the environment `env` (whose focus is ignored), and fails when
no matrix does. -/
def discharge (i : VocabularyItem F E) (env : Neighborhood (List F)) :
    List (List F) → Option (List (List F))
  | [] => none
  | m :: ms =>
    if Applies i ({ env with focus := m } : Neighborhood (List F)) then
      some (subFeatures m i.features.val :: ms)
    else (discharge i env ms).map (m :: ·)

/-- Strict scansion with local Fission at a node bearing the matrices `ms` in the environment
`env` yields the items inserted, in Vocabulary order, and the matrices left over. -/
def scan : RuleSet (VocabularyItem F E) → Neighborhood (List F) → List (List F) →
    List (VocabularyItem F E) × List (List F)
  | [], _, ms => ([], ms)
  | i :: rest, env, ms =>
    match discharge i env ms with
    | some ms' => (scan rest env ms').map (i :: ·) id
    | none => scan rest env ms

/-- `insertions` lists the items scansion inserts. -/
def insertions (items : RuleSet (VocabularyItem F E)) (env : Neighborhood (List F))
    (ms : List (List F)) : List (VocabularyItem F E) :=
  (scan items env ms).1

/-- `residue` lists the matrices scansion leaves, the features no inserted item discharged. -/
def residue (items : RuleSet (VocabularyItem F E)) (env : Neighborhood (List F))
    (ms : List (List F)) : List (List F) :=
  (scan items env ms).2

/-- A node bearing the matrices `ms` in the environment `env` receives these exponents. -/
def scansion (items : RuleSet (VocabularyItem F E)) (env : Neighborhood (List F))
    (ms : List (List F)) : List E :=
  (insertions items env ms).map (·.exponent)

variable {items rest : RuleSet (VocabularyItem F E)} {env : Neighborhood (List F)}
  {i : VocabularyItem F E} {ms ms' : List (List F)}

@[simp] theorem discharge_nil (i : VocabularyItem F E) : discharge i env [] = none := rfl

@[simp] theorem scan_nil (env : Neighborhood (List F)) (ms : List (List F)) :
    scan ([] : RuleSet (VocabularyItem F E)) env ms = ([], ms) := rfl

theorem scan_cons_of_discharge_eq_some (h : discharge i env ms = some ms') :
    scan (i :: rest) env ms = (i :: insertions rest env ms', residue rest env ms') := by
  simp only [scan, h]; rfl

theorem scan_cons_of_discharge_eq_none (h : discharge i env ms = none) :
    scan (i :: rest) env ms = scan rest env ms := by
  simp [scan, h]

/-- Discharge subtracts the item's features, a finite set, from the node's multiset. -/
theorem val_add_discharge : ∀ {ms ms' : List (List F)}, discharge i env ms = some ms' →
    i.features.val + ms'.flatten = (ms.flatten : Multiset F)
  | [], _, h => by simp at h
  | m :: ms, ms', h => by
    unfold discharge at h
    split_ifs at h with hs
    · cases h
      have hle : i.features.val ≤ (m : Multiset F) := Finset.val_le_iff_val_subset.mpr
        fun f hf ↦ by
          simpa [Neighborhood.mem_def] using hs _ (VocabularyItem.mem_features.1 hf)
      rw [List.flatten_cons, List.flatten_cons, ← Multiset.coe_add, ← Multiset.coe_add,
        coe_subFeatures, ← Multiset.add_assoc, Multiset.add_comm i.features.val,
        Multiset.sub_add_cancel hle]
    · obtain ⟨ms'', h'', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [List.flatten_cons, List.flatten_cons, ← Multiset.coe_add, ← Multiset.coe_add,
        ← Multiset.add_assoc, Multiset.add_comm i.features.val, Multiset.add_assoc,
        val_add_discharge h'']

/-- **Conservation.** In the free commutative monoid on the features, the inserted items'
features and the residue sum to the node. -/
theorem bind_insertions_add_residue :
    ∀ (items : RuleSet (VocabularyItem F E)) (ms : List (List F)),
    (insertions items env ms : Multiset (VocabularyItem F E)).bind (·.features.val) +
      ((residue items env ms).flatten : Multiset F) = ms.flatten
  | [], _ => by simp [insertions, residue]
  | i :: rest, ms => by
    cases h : discharge i env ms with
    | none =>
      simpa [insertions, residue, scan_cons_of_discharge_eq_none h] using
        bind_insertions_add_residue rest ms
    | some ms' =>
      rw [insertions, residue, scan_cons_of_discharge_eq_some h]
      dsimp only
      rw [← Multiset.cons_coe, Multiset.cons_bind, Multiset.add_assoc,
        bind_insertions_add_residue rest ms', val_add_discharge h]

/-- **No multiple exponence.** The inserted items' features fit inside the node, so no feature is
discharged more often than the node bears it. -/
theorem bind_insertions_le (items : RuleSet (VocabularyItem F E)) (ms : List (List F)) :
    (insertions items env ms : Multiset (VocabularyItem F E)).bind (·.features.val) ≤
      (ms.flatten : Multiset F) :=
  bind_insertions_add_residue items ms ▸ Multiset.le_add_right _ _

/-- On a node without repetitions the inserted items' features are disjoint, so the items
partition the features they discharge. -/
theorem pairwise_disjoint_insertions (h : ms.flatten.Nodup) :
    (insertions items env ms).Pairwise fun i j ↦ Disjoint i.features j.features := by
  have := Multiset.nodup_of_le (bind_insertions_le (env := env) items ms) (Multiset.coe_nodup.mpr h)
  rw [Multiset.nodup_bind, Multiset.pairwise_coe_iff_pairwise] at this
  exact this.2.imp (Finset.disjoint_val.mp ·)

/-- A node with no matrix receives nothing. -/
@[simp] theorem insertions_nil_right :
    ∀ items : RuleSet (VocabularyItem F E), insertions items env [] = []
  | [] => rfl
  | _ :: rest => insertions_nil_right rest

@[simp] theorem scansion_nil : scansion items env [] = [] := by simp [scansion]

/-- Each item is inserted at most once, in Vocabulary order. -/
theorem insertions_sublist : ∀ (items : RuleSet (VocabularyItem F E)) (ms : List (List F)),
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

theorem scansion_sublist (ms : List (List F)) :
    (scansion items env ms).Sublist (items.map (·.exponent)) :=
  (insertions_sublist items ms).map _

theorem length_scansion_le (ms : List (List F)) :
    (scansion items env ms).length ≤ items.length := by
  simpa using (scansion_sublist (items := items) (env := env) ms).length_le

/-- At a single matrix, an item discharges iff it applies there. -/
theorem discharge_singleton (i : VocabularyItem F E) (m : List F) :
    discharge i env [m] =
      if Applies i ({ env with focus := m } : Neighborhood (List F))
        then some [subFeatures m i.features.val] else none := by
  simp [discharge]

/-- At a single matrix, the first item inserted is the first item that applies there. -/
theorem head?_insertions_singleton (m : List F) : ∀ items : RuleSet (VocabularyItem F E),
    (insertions items env [m]).head? =
      (items.applicable ({ env with focus := m } : Neighborhood (List F))).head?
  | [] => rfl
  | i :: rest => by
    by_cases h : Applies i ({ env with focus := m } : Neighborhood (List F))
    · rw [insertions, scan_cons_of_discharge_eq_some (by rw [discharge_singleton, ite_eq_left h])]
      simp [RuleSet.applicable, h]
    · rw [insertions, scan_cons_of_discharge_eq_none (by rw [discharge_singleton, ite_eq_right h])]
      simpa [insertions, RuleSet.applicable, h] using
        head?_insertions_singleton m rest

/-- On a Vocabulary ordered by decreasing specificity, the first insertion at a single matrix is
the Subset Principle's winner, so scansion agrees with Elsewhere competition where both
apply. -/
theorem head?_scansion_singleton (m : List F)
    (hsorted : items.Pairwise fun i j => j.specificity ≤ i.specificity) :
    (scansion items env [m]).head? =
      (winner? items ({ env with focus := m } : Neighborhood (List F))).map (·.exponent) := by
  rw [scansion, List.head?_map, head?_insertions_singleton, winner?,
    RuleSet.selectBy_eq_head? hsorted]

end DistributedMorphology
