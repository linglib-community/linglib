module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Deletion
public import Linglib.Phonology.OptimalityTheory.Evaluation

/-!
# Positional faithfulness

A positional faithfulness constraint is a faithfulness constraint restricted to a prominent
position, such as the beginning of a word or a root, whose segments it protects. Restricted to
deletion, a candidate is the set of input positions it deletes, and the MAX constraint of a set of
positions counts the deleted positions in it; [on deletions from a string this is MAX restricted to
those positions](##maxAt_eq_maxViolAt) in the sense of McCarthy and Prince's Correspondence Theory.
The deletion of a single position therefore violates exactly the constraints that protect that
position, and single deletions compete through those sets of constraints. [One of them is optimal
under some ranking exactly when the set of constraints protecting its position is minimal among
them](##exists_mem_optimal_positionalMax_iff), and [two of them are both optimal under a ranking
exactly when the same constraints protect both positions](##optimal_eq_pair_positionalMax_iff).

## References

* [beckman-1999]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace OptimalityTheory

/-! ### MAX restricted to a set of positions -/

namespace Constraint

section MaxAt

variable (P : ℕ → Prop) [DecidablePred P]

/-- `maxAt P D` counts the positions of the deletion `D` that lie in `P`, the violations of MAX
restricted to `P`. -/
def maxAt : Constraint (Finset ℕ) := fun D ↦ (D.filter P).card

@[simp] theorem maxAt_empty : maxAt P ∅ = 0 := rfl

@[simp] theorem maxAt_singleton (k : ℕ) : maxAt P {k} = if P k then 1 else 0 := by
  simp only [maxAt, Finset.filter_singleton]
  split_ifs <;> rfl

@[simp] theorem maxAt_true (D : Finset ℕ) : maxAt (fun _ ↦ True) D = D.card := by
  simp [maxAt]

theorem maxAt_insert {k : ℕ} {D : Finset ℕ} (hk : k ∉ D) :
    maxAt P (insert k D) = maxAt P D + if P k then 1 else 0 := by
  simp only [maxAt, Finset.filter_insert]
  split_ifs <;> simp [Finset.card_insert_of_notMem (fun h ↦ hk (Finset.mem_filter.1 h).1)]

/-- On the deletion of one position from a string, `maxAt P` counts the input segments in `P`
that have no correspondent in the output. -/
theorem maxAt_singleton_eq_maxViolAt {α : Type*} {s : List α} (k : Fin s.length) :
    maxAt P {(k : ℕ)} = (Correspondence.Coindexation.eraseIdx s k).maxViolAt P .lhs .rhs := by
  rw [maxAt_singleton, Correspondence.Coindexation.maxViolAt_eraseIdx]

/-- On the deletion of the positions `D` from a string, `maxAt P` counts the input segments in `P`
that have no correspondent in the output. -/
theorem maxAt_eq_maxViolAt {α : Type*} {s : List α} {D : Finset ℕ} (hD : ∀ k ∈ D, k < s.length) :
    maxAt P D = (Correspondence.Coindexation.eraseIdxs s D).maxViolAt P .lhs .rhs :=
  (Correspondence.Coindexation.maxViolAt_eraseIdxs hD P).symm

end MaxAt

end Constraint

/-! ### Families of positional constraints -/

section Positional

variable {ι C : Type*} (P : ι → ℕ → Prop) [∀ i, DecidablePred (P i)]
  (del : C → Finset ℕ)

/-- `positionalMax P del` is MAX restricted to each set of positions `P i`, on candidates that
delete the positions `del c`. -/
def positionalMax (c : C) : ι → ℕ := fun i ↦ Constraint.maxAt (P i) (del c)

@[simp] theorem positionalMax_apply (c : C) (i : ι) :
    positionalMax P del c i = Constraint.maxAt (P i) (del c) := rfl

variable {P del} {c d : C} {k k' : ℕ}

theorem positionalMax_lt_positionalMax_iff (hc : del c = {k}) (hd : del d = {k'}) {i : ι} :
    positionalMax P del c i < positionalMax P del d i ↔ ¬ P i k ∧ P i k' := by
  simp only [positionalMax_apply, hc, hd, Constraint.maxAt_singleton]
  split_ifs <;> simp_all

theorem positionalMax_lt_iff (hc : del c = {k}) (hd : del d = {k'}) :
    positionalMax P del c < positionalMax P del d ↔ {i | P i k} ⊂ {i | P i k'} := by
  rw [Pi.lt_def, Set.ssubset_def, Set.not_subset]
  simp only [positionalMax_lt_positionalMax_iff hc hd]
  simp only [Pi.le_def, positionalMax_apply, hc, hd, Constraint.maxAt_singleton, Set.subset_def]
  refine and_congr (forall_congr' fun i ↦ ?_) (exists_congr fun _ ↦ and_comm)
  split_ifs <;> simp_all

theorem positionalMax_le_iff (hc : del c = {k}) (hd : del d = {k'}) :
    positionalMax P del c ≤ positionalMax P del d ↔ {i | P i k} ⊆ {i | P i k'} := by
  simp only [Pi.le_def, positionalMax_apply, hc, hd, Constraint.maxAt_singleton, Set.subset_def]
  refine forall_congr' fun i ↦ ?_
  split_ifs <;> simp_all

variable [DecidableEq C] {n : ℕ} {cands : Finset C}

theorem optimal_eq_singleton_positionalMax_iff (hcand : cands = {c, d}) (hne : c ≠ d)
    (hc : del c = {k}) (hd : del d = {k'}) (r : Ranking.Enumeration ι n) :
    r.optimal (positionalMax P del) cands = {c} ↔
      ∃ i, P i k' ∧ ¬ P i k ∧ ∀ j, P j k → ¬ P j k' → r.Dominates i j := by
  rw [Ranking.Enumeration.optimal_eq_singleton_iff_pair hcand hne,
    Ranking.Enumeration.profile_lt_iff_exists_dominates]
  simp only [positionalMax_lt_positionalMax_iff hc hd, positionalMax_lt_positionalMax_iff hd hc]
  exact exists_congr fun _ ↦ ⟨fun ⟨⟨h, h'⟩, hr⟩ ↦ ⟨h', h, fun j hj hj' ↦ hr j ⟨hj', hj⟩⟩,
    fun ⟨h', h, hr⟩ ↦ ⟨⟨h, h'⟩, fun j ⟨hj', hj⟩ ↦ hr j hj hj'⟩⟩

/-- Of two single deletions, the one whose position is protected by a proper subset of the
constraints protecting the other's is the sole winner under every ranking. -/
theorem optimal_eq_singleton_positionalMax_of_ssubset (hcand : cands = {c, d}) (hc : del c = {k})
    (hd : del d = {k'}) (h : {i | P i k} ⊂ {i | P i k'}) (r : Ranking.Enumeration ι n) :
    r.optimal (positionalMax P del) cands = {c} :=
  Ranking.Enumeration.optimal_eq_singleton_of_forall_lt (by simp [hcand]) fun e he hne ↦ by
    obtain rfl : e = d := by simpa [hcand, hne] using he
    exact (positionalMax_lt_iff hc hd).2 h

theorem optimal_eq_pair_positionalMax_iff (hcand : cands = {c, d}) (hc : del c = {k})
    (hd : del d = {k'}) (r : Ranking.Enumeration ι n) :
    r.optimal (positionalMax P del) cands = {c, d} ↔
      {i | P i k} = {i | P i k'} := by
  rw [Ranking.Enumeration.optimal_eq_pair_iff hcand, funext_iff, Set.ext_iff]
  refine forall_congr' fun i ↦ ?_
  simp only [positionalMax_apply, hc, hd, Constraint.maxAt_singleton]
  split_ifs <;> simp_all

variable [Fintype ι] (hn : Fintype.card ι = n)
include hn

omit [DecidableEq C] in
/-- Among deletions of one position each, one is optimal under some ranking exactly when the
constraints protecting its position are minimal among the sets protecting each. -/
theorem exists_mem_optimal_positionalMax_iff {pos : C → ℕ} :
    (∃ r : Ranking.Enumeration ι n,
        c ∈ r.optimal (positionalMax P fun d ↦ {pos d}) cands) ↔
      MinimalFor (· ∈ cands) (fun d ↦ {i | P i (pos d)}) c := by
  rw [Ranking.Enumeration.exists_mem_optimal_iff_minimalFor hn fun d _ i ↦ by
    rw [positionalMax_apply, Constraint.maxAt_singleton]; split_ifs <;> simp]
  exact and_congr_right fun _ ↦ forall_congr' fun d ↦ imp_congr_right fun _ ↦
    imp_congr (positionalMax_le_iff rfl rfl) (positionalMax_le_iff rfl rfl)

theorem exists_optimal_eq_singleton_positionalMax_iff (hcand : cands = {c, d})
    (hne : c ≠ d) (hc : del c = {k}) (hd : del d = {k'}) :
    (∃ r : Ranking.Enumeration ι n, r.optimal (positionalMax P del) cands =
        {c}) ↔
      ¬ {i | P i k'} ⊆ {i | P i k} := by
  rw [Ranking.Enumeration.exists_optimal_eq_singleton_iff_pair hn hcand hne, Set.not_subset]
  simp only [positionalMax_lt_positionalMax_iff hc hd]
  exact exists_congr fun _ ↦ and_comm

end Positional

end OptimalityTheory
