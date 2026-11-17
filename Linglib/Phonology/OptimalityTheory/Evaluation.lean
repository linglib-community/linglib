module

public import Linglib.Phonology.OptimalityTheory.Filtration

/-!
# Evaluation under a ranking

Under a ranking, a candidate's violations are read in rank order and compared lexicographically:
the optimal candidates are those of least profile, the *harmonic ordering of forms* of
[prince-smolensky-1993]. Violations are given by a map `v`, with `v c k` the number of violations
of the constraint `k` by the candidate `c`, and the candidates by a finite set.

One candidate [beats](##OptimalityTheory.Ranking.Enumeration.profile_lt_iff_exists_dominates)
another iff some constraint preferring it dominates every constraint preferring the other, ties
[do not depend on the ranking](##OptimalityTheory.Ranking.Enumeration.mem_optimal_iff_of_mem),
and the optimal candidates are
[the survivors of filtration](##OptimalityTheory.Ranking.Enumeration.optimal_eq_filtration)
along the ranking.

## References

* [prince-smolensky-1993]
* [prince-2002]
-/

@[expose] public section

namespace OptimalityTheory.Ranking.Enumeration

variable {C ι : Type*} {n : ℕ} (σ : Ranking.Enumeration ι n) (v : C → ι → ℕ) (s : Finset C)
  {c d : C}

/-- The violations of a candidate in rank order, compared lexicographically. -/
def profile (c : C) : Lex (Fin n → ℕ) := toLex fun p ↦ v c (σ p)

@[simp] theorem profile_apply (c : C) (p : Fin n) : σ.profile v c p = v c (σ p) := rfl

/-- The optimal candidates under a ranking: those of least profile. -/
def optimal : Finset C := s.argmin (σ.profile v)

variable {σ v s}

theorem optimal_eq_tableau :
    σ.optimal v s = (Tableau.ofRanking (fun k c ↦ v c k) σ s).optimal := rfl

theorem mem_optimal_iff :
    c ∈ σ.optimal v s ↔ c ∈ s ∧ ∀ d ∈ s, σ.profile v c ≤ σ.profile v d :=
  Finset.mem_argmin

theorem optimal_subset : σ.optimal v s ⊆ s := Finset.argmin_subset ..

theorem optimal_nonempty (h : s.Nonempty) : (σ.optimal v s).Nonempty :=
  Tableau.optimal_nonempty (t := Tableau.ofRanking (fun k c ↦ v c k) σ s) h

/-- The optimal candidates are the survivors of filtration along the ranking. -/
theorem optimal_eq_filtration : σ.optimal v s = filtration v s (List.ofFn σ) :=
  Tableau.optimal_ofRanking_eq_filtration (fun k c ↦ v c k) σ s

/-- One candidate beats another iff some constraint preferring it dominates every constraint
preferring the other. -/
theorem profile_lt_iff_exists_dominates :
    σ.profile v c < σ.profile v d ↔
      ∃ i, v c i < v d i ∧ ∀ j, v d j < v c j → σ.Dominates i j :=
  Tableau.ofRanking_profile_lt_iff_exists_dominates (con := fun k c ↦ v c k) (candidates := ∅)

/-- A candidate is the sole winner iff it is a candidate and, against each competitor, some
constraint preferring it dominates every constraint preferring the competitor. -/
theorem optimal_eq_singleton_iff :
    σ.optimal v s = {c} ↔ c ∈ s ∧ ∀ d ∈ s, d ≠ c →
      ∃ i, v c i < v d i ∧ ∀ j, v d j < v c j → σ.Dominates i j :=
  Tableau.ofRanking_optimal_eq_singleton_iff (con := fun k c ↦ v c k)

/-- Ties do not depend on the ranking: beside a winner, the winners are the candidates with the
same violations. -/
theorem mem_optimal_iff_of_mem (hc : c ∈ σ.optimal v s) :
    d ∈ σ.optimal v s ↔ d ∈ s ∧ v d = v c :=
  (Tableau.ofRanking_mem_optimal_iff_of_mem (con := fun k c ↦ v c k) hc).trans
    (and_congr_right fun _ ↦ funext_iff.symm)

/-- A winner is the sole winner iff no other candidate has the same violations. -/
theorem optimal_eq_singleton_iff_of_mem (hc : c ∈ σ.optimal v s) :
    σ.optimal v s = {c} ↔ ∀ d ∈ s, v d = v c → d = c :=
  (Tableau.ofRanking_optimal_eq_singleton_iff_of_mem (con := fun k c ↦ v c k) hc).trans
    (forall₂_congr fun _ _ ↦ imp_congr_left funext_iff.symm)

/-- A candidate is the sole winner under every ranking that extends a relation `R` on the
constraints, such as the Hasse diagram an analysis prints, if against each competitor some
constraint preferring it is `R`-above every constraint preferring the competitor. -/
theorem optimal_eq_singleton_of_rel {R : ι → ι → Prop} (hr : R ≤ σ.Dominates) (hc : c ∈ s)
    (h : ∀ d ∈ s, d ≠ c → ∃ i, v c i < v d i ∧ ∀ j, v d j < v c j → R i j) :
    σ.optimal v s = {c} :=
  Tableau.ofRanking_optimal_eq_singleton_of_rel (con := fun k c ↦ v c k) hr hc h

/-- A candidate that violates every constraint at least as often as a competitor, and some
constraint more often, is *harmonically bounded*: it is optimal under no ranking. -/
theorem notMem_optimal_of_lt (hc : c ∈ s) (hlt : v c < v d) : d ∉ σ.optimal v s :=
  Tableau.ofRanking_notMem_optimal_of_lt (con := fun k c ↦ v c k) hc hlt

theorem optimal_eq_singleton_of_forall_lt (hc : c ∈ s) (hlt : ∀ d ∈ s, d ≠ c → v c < v d) :
    σ.optimal v s = {c} :=
  Tableau.ofRanking_optimal_eq_singleton_of_forall_lt (con := fun k c ↦ v c k) hc hlt

/-- A candidate with no violations wins under every ranking. -/
theorem zero_mem_optimal (hc : c ∈ s) (hzero : v c = 0) : c ∈ σ.optimal v s :=
  Tableau.ofRanking_zero_mem_optimal (con := fun k c ↦ v c k) hc (congrFun hzero)

/-- If some candidate satisfies every constraint, then under every ranking so does every
winner. -/
theorem eq_zero_of_mem_optimal (hc : c ∈ σ.optimal v s) (hd : d ∈ s) (h0 : v d = 0) : v c = 0 :=
  funext <| Tableau.ofRanking_eq_zero_of_mem_optimal (con := fun k c ↦ v c k) hc hd (congrFun h0)

/-- If the constraints `U` dominate all the others, a candidate satisfying all of `U` beats a
candidate violating any of them. -/
theorem profile_lt_of_forall_dominates {U : Set ι} (hU : ∀ i ∈ U, ∀ j ∉ U, σ.Dominates i j)
    (hc : ∀ i ∈ U, v c i = 0) {i : ι} (hi : i ∈ U) (hd : v d i ≠ 0) :
    σ.profile v c < σ.profile v d :=
  Tableau.ofRanking_profile_lt_of_forall_dominates (con := fun k c ↦ v c k) (candidates := ∅)
    hU hc hi hd

/-- Optimality transfers along constraint-wise bounds: a candidate `d` of a second candidate set
that violates each constraint no more than a winner `c` of the first is itself a winner, provided
every candidate of the second set violates each constraint at least as much as some candidate of
the first. -/
theorem mem_optimal_of_forall_le {C' : Type*} {v' : C' → ι → ℕ} {s' : Finset C'} {d : C'}
    (hc : c ∈ σ.optimal v s) (hd : d ∈ s') (hdc : v' d ≤ v c)
    (h : ∀ d' ∈ s', ∃ c' ∈ s, v c' ≤ v' d') : d ∈ σ.optimal v' s' :=
  Tableau.ofRanking_mem_optimal_of_forall_le (con := fun k c ↦ v c k)
    (con' := fun k c ↦ v' c k) hc hd hdc h

/-- If some candidate violates none of the constraints a ranking puts above its last, the winners
are the candidates violating none of them that do best on the last. -/
theorem optimal_eq_argmin_filter [Fintype ι] [DecidableEq ι] {σ : Ranking.Enumeration ι (n + 1)}
    (h : ∃ c ∈ s, ∀ i ≠ σ (Fin.last n), v c i = 0) :
    σ.optimal v s =
      (s.filter fun c ↦ ∀ i ≠ σ (Fin.last n), v c i = 0).argmin (v · (σ (Fin.last n))) :=
  Tableau.ofRanking_optimal_eq_argmin_filter (con := fun k c ↦ v c k) h

section Bounding

variable [DecidableEq C] [Fintype ι] (hn : Fintype.card ι = n)
include hn

/-- A candidate wins against its only competitor under some ranking iff the competitor does not
harmonically bound it. -/
theorem exists_mem_optimal_iff_pair (hs : s = {c, d}) :
    (∃ σ : Ranking.Enumeration ι n, c ∈ σ.optimal v s) ↔ ¬ v d < v c :=
  Tableau.exists_mem_ofRanking_optimal_iff_pair (con := fun k c ↦ v c k) hn hs

/-- A candidate is the sole winner against its only competitor under some ranking iff some
constraint prefers it. -/
theorem exists_optimal_eq_singleton_iff_pair (hs : s = {c, d}) (hne : c ≠ d) :
    (∃ σ : Ranking.Enumeration ι n, σ.optimal v s = {c}) ↔ ∃ i, v c i < v d i :=
  Tableau.exists_ofRanking_optimal_eq_singleton_iff_pair (con := fun k c ↦ v c k) hn hs hne

omit [DecidableEq C] in
/-- Among candidates that violate each constraint at most once, a candidate wins under some
ranking iff no candidate's violations are a proper part of its own. -/
theorem exists_mem_optimal_iff_minimalFor (h : ∀ d ∈ s, ∀ i, v d i ≤ 1) :
    (∃ σ : Ranking.Enumeration ι n, c ∈ σ.optimal v s) ↔ MinimalFor (· ∈ s) v c :=
  Tableau.exists_mem_ofRanking_optimal_iff_minimalFor (con := fun k c ↦ v c k) hn h

end Bounding

/-- Against its only competitor a candidate is the sole winner iff its profile is less. -/
theorem optimal_eq_singleton_iff_pair [DecidableEq C] (hs : s = {c, d}) (hne : c ≠ d) :
    σ.optimal v s = {c} ↔ σ.profile v c < σ.profile v d :=
  Tableau.optimal_eq_singleton_iff_pair (t := Tableau.ofRanking (fun k c ↦ v c k) σ s) hs hne

/-- Against its only competitor a candidate wins iff its profile is not greater. -/
theorem mem_optimal_iff_pair [DecidableEq C] (hs : s = {c, d}) :
    c ∈ σ.optimal v s ↔ ¬ σ.profile v d < σ.profile v c :=
  Tableau.mem_optimal_iff_pair (t := Tableau.ofRanking (fun k c ↦ v c k) σ s) hs

/-- Two candidates with no other competitor both win iff no constraint tells them apart. -/
theorem optimal_eq_pair_iff [DecidableEq C] (hs : s = {c, d}) :
    σ.optimal v s = {c, d} ↔ v c = v d :=
  (Tableau.ofRanking_optimal_eq_pair_iff (con := fun k c ↦ v c k) hs).trans funext_iff.symm

end OptimalityTheory.Ranking.Enumeration
