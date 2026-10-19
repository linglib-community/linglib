module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Erase
public import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Positional faithfulness

A positional faithfulness constraint is a faithfulness constraint restricted to a prominent
position, such as the beginning of a word or a root, whose segments it protects. Restricted to
deletion, a candidate is the set of input positions it deletes, and the MAX constraint of a set of
positions counts the deleted positions in it. The deletion of a single position therefore violates
exactly the constraints that protect that position, and two single deletions compete through those
sets of constraints: one of them is optimal under some ranking exactly when the constraints
protecting the other position are not a proper subset of those protecting its own.

## Main definitions

* `OptimalityTheory.maxAt`: MAX restricted to a set of positions, on deletions.
* `OptimalityTheory.positionalMax`: a family of such constraints, on candidates that delete
  positions.

## Main results

* `OptimalityTheory.maxAt_singleton_eq_maxViolAt`: on the deletion of one position from a string,
  `maxAt` is MAX restricted to the positions in the sense of Correspondence Theory.
* `OptimalityTheory.exists_mem_optimal_positionalMax_iff`: of two single deletions, one is optimal
  under some ranking iff the constraints protecting the other position are not a proper subset of
  those protecting its own.

## References

* [beckman-1999]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace OptimalityTheory

/-! ### MAX restricted to a set of positions -/

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

/-- Deleting one more position adds a violation exactly when the position lies in `P`. -/
theorem maxAt_insert {k : ℕ} {D : Finset ℕ} (hk : k ∉ D) :
    maxAt P (insert k D) = maxAt P D + if P k then 1 else 0 := by
  simp only [maxAt, Finset.filter_insert]
  split_ifs <;> simp [Finset.card_insert_of_notMem (fun h ↦ hk (Finset.mem_filter.1 h).1)]

/-- On the deletion of one position from a string, `maxAt P` counts the input segments in `P`
that have no correspondent in the output. -/
theorem maxAt_singleton_eq_maxViolAt {α : Type*} {s : List α} {k : ℕ} (hk : k < s.length) :
    maxAt P {k} = (Correspondence.eraseIdx s k).maxViolAt P .lhs .rhs := by
  rw [maxAt_singleton, Correspondence.maxViolAt_eraseIdx hk]

end MaxAt

/-! ### Families of positional constraints -/

section Positional

variable {ι C : Type*} (P : ι → ℕ → Prop) [∀ i, DecidablePred (P i)]
  (del : C → Finset ℕ)

/-- `positionalMax P del` is MAX restricted to each set of positions `P i`, on candidates that
delete the positions `del c`. -/
def positionalMax : ConstraintSet C ι := fun i c ↦ maxAt (P i) (del c)

@[simp] theorem positionalMax_apply (i : ι) (c : C) :
    positionalMax P del i c = maxAt (P i) (del c) := rfl

variable {P del} {c d : C} {k k' : ℕ}

theorem positionalMax_lt_positionalMax_iff (hc : del c = {k}) (hd : del d = {k'}) {i : ι} :
    positionalMax P del i c < positionalMax P del i d ↔ ¬ P i k ∧ P i k' := by
  simp only [positionalMax_apply, hc, hd, maxAt_singleton]
  split_ifs <;> simp_all

/-- One single deletion is below another on every constraint exactly when the constraints
protecting its position are a proper subset of those protecting the other's. -/
theorem positionalMax_lt_iff (hc : del c = {k}) (hd : del d = {k'}) :
    (positionalMax P del · c) < (positionalMax P del · d) ↔ {i | P i k} ⊂ {i | P i k'} := by
  rw [Pi.lt_def, Set.ssubset_def, Set.not_subset]
  simp only [positionalMax_lt_positionalMax_iff hc hd]
  simp only [Pi.le_def, positionalMax_apply, hc, hd, maxAt_singleton, Set.subset_def]
  refine and_congr (forall_congr' fun i ↦ ?_) (exists_congr fun _ ↦ and_comm)
  split_ifs <;> simp_all

variable [DecidableEq C] {n : ℕ} {cands : Finset C}

/-- Of two single deletions, one is the sole optimum under a ranking exactly when some constraint
protecting only the other position outranks every constraint protecting only its own. -/
theorem optimal_eq_singleton_positionalMax_iff (hcand : cands = {c, d}) (hne : c ≠ d)
    (hc : del c = {k}) (hd : del d = {k'}) (r : Ranking ι n) :
    (Tableau.ofRanking (positionalMax P del) r cands).optimal = {c} ↔
      ∃ i, P i k' ∧ ¬ P i k ∧ ∀ j, P j k → ¬ P j k' → r.Dominates i j := by
  rw [Tableau.optimal_eq_singleton_iff_pair hcand hne,
    Tableau.ofRanking_profile_lt_iff_exists_dominates]
  simp only [positionalMax_lt_positionalMax_iff hc hd, positionalMax_lt_positionalMax_iff hd hc]
  exact exists_congr fun _ ↦ ⟨fun ⟨⟨h, h'⟩, hr⟩ ↦ ⟨h', h, fun j hj hj' ↦ hr j ⟨hj', hj⟩⟩,
    fun ⟨h', h, hr⟩ ↦ ⟨⟨h, h'⟩, fun j ⟨hj', hj⟩ ↦ hr j hj hj'⟩⟩

variable [Fintype ι] (hn : Fintype.card ι = n)
include hn

/-- Of two single deletions, one is optimal under some ranking exactly when the constraints
protecting the other position are not a proper subset of those protecting its own. -/
theorem exists_mem_optimal_positionalMax_iff (hcand : cands = {c, d})
    (hc : del c = {k}) (hd : del d = {k'}) :
    (∃ r : Ranking ι n, c ∈ (Tableau.ofRanking (positionalMax P del) r cands).optimal) ↔
      ¬ {i | P i k'} ⊂ {i | P i k} := by
  rw [Tableau.exists_mem_ofRanking_optimal_iff_pair hn hcand, positionalMax_lt_iff hd hc]

/-- Of two single deletions, one is the sole optimum under some ranking exactly when some
constraint protects the other position and not its own. -/
theorem exists_optimal_eq_singleton_positionalMax_iff (hcand : cands = {c, d})
    (hne : c ≠ d) (hc : del c = {k}) (hd : del d = {k'}) :
    (∃ r : Ranking ι n, (Tableau.ofRanking (positionalMax P del) r cands).optimal = {c}) ↔
      ¬ {i | P i k'} ⊆ {i | P i k} := by
  rw [Tableau.exists_ofRanking_optimal_eq_singleton_iff_pair hn hcand hne, Set.not_subset]
  simp only [positionalMax_lt_positionalMax_iff hc hd]
  exact exists_congr fun _ ↦ and_comm

end Positional

end OptimalityTheory
