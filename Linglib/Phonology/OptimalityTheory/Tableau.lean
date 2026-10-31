/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Ranking
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Core.Order.Argmax
public import Linglib.Core.Order.PiLex
public import Mathlib.Algebra.Order.Group.PiLex

/-!
# Tableaux

An Optimality-theoretic tableau, as Prince and Smolensky define it, evaluates a finite set of
candidates by constraints in rank order. The violations of a candidate, read in rank order, form
its *violation profile*, and profiles are compared lexicographically, which is Riggle's harmonic
inequality: the highest-ranked constraint on which two candidates differ decides between them.
The winners of a tableau are the candidates of least profile (`Tableau.optimal`), the
`Finset.argmin` of `Tableau.profile` over the candidates, and a candidate is optimal when it
belongs to this set. Evaluation proceeds constraint by constraint (`Tableau.optimal_tail`): the
winners are the winners under the lower constraints among the candidates that do best on the top
one, and a constraint that rates every candidate alike changes nothing
(`Tableau.optimal_ofList_append_of_forall_eq`).

## Main definitions

* `ViolationProfile n`: the violation vector `Fin n → ℕ` under its lexicographic order.
* `Tableau C n`: a finite set of candidates and `n` constraints in rank order, position `0`
  most dominant.
* `Tableau.profile`, `Tableau.optimal`: a candidate's violation profile, and the set of winners.
* `Tableau.ofRanking con r candidates`: the tableau of a constraint set under a ranking, whose
  constraint at rank position `p` is `con (r p)`.
* `Tableau.ofList`, `Tableau.ofOrder`: the tableau of a list of constraints in rank order, and
  the tableau of a printed table, a column order of labels and the marks in each cell.
* `Tableau.tail`: the candidates that do best on the top constraint, under the constraints below
  it.

## Main statements

* `Tableau.mem_optimal_iff`: a winner is a candidate whose profile is at most every candidate's.
* `Tableau.optimal_eq_singleton_iff`: a tableau has a sole winner iff that candidate's profile
  is strictly below every other candidate's.
* `Tableau.ofRanking_profile_lt_iff_exists_dominates`: under a ranking, one candidate beats
  another iff some constraint preferring it dominates every constraint preferring the other.
* `Tableau.ofRanking_notMem_optimal_of_lt`: a candidate that violates every constraint at least
  as often as a competitor, and some more often, wins under no ranking.
* `Tableau.exists_mem_ofRanking_optimal_iff_pair`: against a single competitor, a candidate wins
  under some ranking iff the competitor does not bound it in this way.
* `Tableau.ofRanking_optimal_eq_argmin_filter`: when some candidate satisfies every constraint
  above the last, the winners are the candidates satisfying all of them that do best on the last.
* `Tableau.optimal_tail`: the winners of a tableau are the winners of its tail.
* `Tableau.optimal_ofList_antifaithful`: under `¬F ≫ F`, the winners are the candidates that
  violate `F` least among those violating it at all.

## Implementation notes

* Rank position `0` is the most dominant constraint, so `Tableau.profile` is `toLex` of the
  violation vector and mathlib's lexicographic order on `Fin n → ℕ` is strict domination.
* Optimality is membership in `Tableau.optimal` rather than a separate predicate, and
  `Tableau.mem_optimal_iff` unfolds it.
* `Tableau.ofList` takes its number of constraints from the length of the list and is
  `Tableau.ofRanking` under the identity ranking; `Tableau.ofOrder` takes its number of
  constraints from the length of the column order and every inhabitant of `C` as a candidate.

## References

* [A. Prince and P. Smolensky, *Optimality Theory: Constraint Interaction in Generative Grammar*
  (1993)][prince-smolensky-1993]
* [J. Riggle, *Violation Semirings in Optimality Theory* (2009)][riggle-2009b]
* [J. D. Alderete, *Dominance Effects as Trans-derivational Anti-faithfulness*
  (2001)][alderete-2001]
-/

@[expose] public section

namespace OptimalityTheory

/-- A fixed-length violation profile, the violation vector `Fin n → ℕ` under its lexicographic
order. -/
abbrev ViolationProfile (n : ℕ) := Lex (Fin n → ℕ)

/-- An *Optimality-theoretic tableau*: a finite set of candidates and the constraints that
evaluate them, in rank order. -/
structure Tableau (C : Type*) (n : ℕ) where
  /-- The candidates. -/
  candidates : Finset C
  /-- The constraint at each rank position, position `0` most dominant. -/
  constraints : ConstraintSet C (Fin n)

namespace Tableau

variable {C : Type*} {n : ℕ} (t : Tableau C n) (c : C)

/-- The *violation profile* of a candidate: its violations read in rank order, under the
lexicographic order. -/
def profile : ViolationProfile n := toLex fun p ↦ t.constraints p c

@[simp] theorem profile_apply (p : Fin n) : t.profile c p = t.constraints p c := rfl

/-- The winners of a tableau, the candidates of least profile. -/
def optimal : Finset C := t.candidates.argmin t.profile

variable {t c} {d m : C}

/-- A winner is a candidate whose profile is at most that of every candidate. -/
theorem mem_optimal_iff :
    c ∈ t.optimal ↔ c ∈ t.candidates ∧ ∀ d ∈ t.candidates, t.profile c ≤ t.profile d :=
  Finset.mem_argmin

theorem optimal_subset : t.optimal ⊆ t.candidates :=
  Finset.argmin_subset

/-- A tableau with a candidate has a winner. -/
theorem optimal_nonempty (h : t.candidates.Nonempty) : t.optimal.Nonempty :=
  Finset.argmin_nonempty h

theorem le_of_mem_optimal (hc : c ∈ t.optimal) (hd : d ∈ t.candidates) :
    t.profile c ≤ t.profile d :=
  (mem_optimal_iff.1 hc).2 d hd

/-- A tableau has the sole winner `m` iff `m` is a candidate whose profile is strictly below that
of every other candidate. -/
theorem optimal_eq_singleton_iff :
    t.optimal = {m} ↔ m ∈ t.candidates ∧ ∀ c ∈ t.candidates, c ≠ m → t.profile m < t.profile c :=
  Finset.argmin_eq_singleton_iff

@[simp] theorem optimal_singleton (hc : t.candidates = {c}) : t.optimal = {c} :=
  optimal_eq_singleton_iff.2 ⟨by simp [hc], fun _ hd hdc ↦ absurd (by simpa [hc] using hd) hdc⟩

/-- A candidate whose profile is strictly above that of a competitor is not a winner. -/
theorem notMem_optimal_of_lt (hc : c ∈ t.candidates) (h : t.profile c < t.profile d) :
    d ∉ t.optimal :=
  fun hd ↦ (le_of_mem_optimal hd hc).not_gt h

theorem mem_optimal_of_profile_eq_zero (hc : c ∈ t.candidates) (h0 : t.profile c = 0) :
    c ∈ t.optimal :=
  mem_optimal_iff.2 ⟨hc, fun _ _ ↦ h0 ▸ bot_le⟩

theorem profile_eq_zero_of_mem_optimal (hc : c ∈ t.optimal) (hd : d ∈ t.candidates)
    (h0 : t.profile d = 0) : t.profile c = 0 :=
  le_antisymm (h0 ▸ le_of_mem_optimal hc hd) bot_le

/-- A winner does at least as well as every candidate on the top constraint, so that if some
candidate satisfies the top constraint, every winner does. -/
theorem constraints_zero_le_of_mem_optimal {t : Tableau C (n + 1)} (hc : c ∈ t.optimal)
    (hd : d ∈ t.candidates) : t.constraints 0 c ≤ t.constraints 0 d :=
  Pi.apply_le_of_toLex (x := (t.constraints · c)) (le_of_mem_optimal hc hd) fun j hj ↦
    absurd hj (Fin.not_lt_zero j)

section Pair

variable [DecidableEq C]

theorem optimal_eq_singleton_iff_pair (hcand : t.candidates = {c, d}) (hne : c ≠ d) :
    t.optimal = {c} ↔ t.profile c < t.profile d := by
  simp [optimal_eq_singleton_iff, hcand, hne.symm]

theorem mem_optimal_iff_pair (hcand : t.candidates = {c, d}) :
    c ∈ t.optimal ↔ ¬ t.profile d < t.profile c := by
  simp [mem_optimal_iff, hcand]

end Pair

/-! ### Tableau constructors -/

section Constructors

variable {ι : Type*} (con : ConstraintSet C ι) (r : Ranking ι n) (candidates : Finset C)
  (ranking : List (Constraint C))

/-- The tableau of a constraint set `con` under a ranking `r`: the constraint at rank position
`p` is `con (r p)`, so that coordinate `0` of the profile is the most dominant constraint. -/
def ofRanking : Tableau C n := ⟨candidates, con ∘ r⟩

/-- The tableau of a list of constraints in rank order, position `0` most dominant:
`Tableau.ofRanking` under the identity ranking. -/
def ofList : Tableau C ranking.length := ofRanking ranking.get (Equiv.refl _) candidates

@[simp] theorem ofRanking_candidates : (ofRanking con r candidates).candidates = candidates := rfl

@[simp] theorem ofRanking_constraints : (ofRanking con r candidates).constraints = con ∘ r := rfl

@[simp] theorem ofList_candidates : (ofList candidates ranking).candidates = candidates := rfl

@[simp] theorem ofList_constraints : (ofList candidates ranking).constraints = ranking.get := rfl

variable {con r candidates}

/-- Under a ranking, one candidate beats another iff some constraint preferring it dominates
every constraint preferring the other. -/
theorem ofRanking_profile_lt_iff_exists_dominates :
    (ofRanking con r candidates).profile c < (ofRanking con r candidates).profile d ↔
      ∃ i, con i c < con i d ∧ ∀ j, con j d < con j c → r.Dominates i j :=
  Pi.toLex_comp_lt_iff_exists r (v := (con · c)) (w := (con · d))

/-- A candidate is the sole winner under a ranking iff it is a candidate and, against each
competitor, some constraint preferring it dominates every constraint preferring the
competitor. -/
theorem ofRanking_optimal_eq_singleton_iff :
    (ofRanking con r candidates).optimal = {c} ↔ c ∈ candidates ∧ ∀ d ∈ candidates, d ≠ c →
      ∃ i, con i c < con i d ∧ ∀ j, con j d < con j c → r.Dominates i j := by
  simp only [optimal_eq_singleton_iff, ofRanking_candidates,
    ofRanking_profile_lt_iff_exists_dominates]

/-- A candidate that violates every constraint at least as often as a competitor, and some
constraint more often, is *harmonically bounded*: it is optimal under no ranking of the
constraint set. -/
theorem ofRanking_notMem_optimal_of_lt (hc : c ∈ candidates) (hlt : (con · c) < (con · d)) :
    d ∉ (ofRanking con r candidates).optimal :=
  notMem_optimal_of_lt hc (Pi.toLex_comp_strictMono r hlt)

theorem ofRanking_optimal_eq_singleton_of_forall_lt (hc : c ∈ candidates)
    (hlt : ∀ d ∈ candidates, d ≠ c → (con · c) < (con · d)) :
    (ofRanking con r candidates).optimal = {c} :=
  optimal_eq_singleton_iff.2 ⟨hc, fun d hd hne ↦ Pi.toLex_comp_strictMono r (hlt d hd hne)⟩

/-- A candidate with no violations on the constraint set wins under every ranking of it. -/
theorem ofRanking_zero_mem_optimal (hc : c ∈ candidates) (hzero : ∀ i, con i c = 0) :
    c ∈ (ofRanking con r candidates).optimal :=
  mem_optimal_of_profile_eq_zero hc (funext fun p ↦ hzero (r p))

/-- If some candidate satisfies every constraint of the set, then under every ranking so does
every winner. -/
theorem ofRanking_eq_zero_of_mem_optimal (hc : c ∈ (ofRanking con r candidates).optimal)
    (hd : d ∈ candidates) (h0 : ∀ i, con i d = 0) (i : ι) : con i c = 0 := by
  have h := profile_eq_zero_of_mem_optimal hc hd (funext fun p ↦ h0 (r p))
  simpa using show con (r (r.symm i)) c = 0 from congrFun h (r.symm i)

/-- Optimality transfers along constraint-wise bounds. Under any ranking, a candidate `d` of a
second tableau that violates each constraint no more than a winner `c` of the first is itself a
winner, provided that every candidate of the second tableau violates each constraint at least as
much as some candidate of the first. -/
theorem ofRanking_mem_optimal_of_forall_le {C' : Type*} {con' : ConstraintSet C' ι}
    {candidates' : Finset C'} {d : C'} (hc : c ∈ (ofRanking con r candidates).optimal)
    (hd : d ∈ candidates') (hdc : ∀ i, con' i d ≤ con i c)
    (h : ∀ d' ∈ candidates', ∃ c' ∈ candidates, ∀ i, con i c' ≤ con' i d') :
    d ∈ (ofRanking con' r candidates').optimal := by
  have hm := (Pi.toLex_comp_strictMono r (β := ℕ)).monotone
  refine mem_optimal_iff.2 ⟨hd, fun d' hd' ↦ ?_⟩
  obtain ⟨c', hc', hle⟩ := h d' hd'
  exact (hm (show (con' · d) ≤ (con · c) from hdc)).trans
    ((le_of_mem_optimal hc hc').trans (hm (show (con · c') ≤ (con' · d') from hle)))

/-- If some candidate violates none of the constraints a ranking puts above its last, the winners
are the candidates violating none of them that do best on the last. -/
theorem ofRanking_optimal_eq_argmin_filter [Fintype ι] [DecidableEq ι] {r : Ranking ι (n + 1)}
    (h : ∃ c ∈ candidates, ∀ i ≠ r (Fin.last n), con i c = 0) :
    (ofRanking con r candidates).optimal =
      (candidates.filter fun c ↦ ∀ i ≠ r (Fin.last n), con i c = 0).argmin
        (con (r (Fin.last n))) := by
  set j := r (Fin.last n)
  have hr : ∀ i ≠ j, r.Dominates i j := fun i hi ↦ by
    rw [Ranking.Dominates, Equiv.symm_apply_apply, Fin.lt_last_iff_ne_last]
    exact fun h ↦ hi (r.symm_apply_eq.1 h)
  obtain ⟨m, hm, hm0⟩ := h
  ext c
  simp only [mem_optimal_iff, ofRanking_candidates, ← not_lt,
    ofRanking_profile_lt_iff_exists_dominates, Finset.mem_argmin, Finset.mem_filter, and_imp]
  constructor
  · rintro ⟨hc, hopt⟩
    have hc0 : ∀ i ≠ j, con i c = 0 := fun i hi ↦ by
      by_contra hne
      refine hopt m hm ⟨i, by rw [hm0 i hi]; omega, fun k hk ↦ ?_⟩
      obtain rfl : k = j := by_contra fun hkj ↦ by simp [hm0 k hkj] at hk
      exact hr i hi
    refine ⟨⟨hc, hc0⟩, fun d hd hd0 hlt ↦ hopt d hd ⟨j, hlt, fun k hk ↦ ?_⟩⟩
    obtain rfl | hkj := eq_or_ne k j
    · exact absurd hk hlt.not_gt
    · simp [hd0 k hkj] at hk
  · rintro ⟨⟨hc, hc0⟩, hmin⟩
    refine ⟨hc, fun d hd ⟨i, hi, hdom⟩ ↦ ?_⟩
    obtain rfl : i = j := by_contra fun hij ↦ by simp [hc0 i hij] at hi
    by_cases hd0 : ∀ k ≠ j, con k d = 0
    · exact hmin d hd hd0 hi
    · push Not at hd0
      obtain ⟨k, hk, hpos⟩ := hd0
      exact asymm (hdom k (by rw [hc0 k hk]; omega)) (hr k hk)

section Bounding

variable [DecidableEq C] [Fintype ι] (hn : Fintype.card ι = n)
include hn

/-- A candidate wins against its only competitor under some ranking iff the competitor does not
harmonically bound it. -/
theorem exists_mem_ofRanking_optimal_iff_pair (hcand : candidates = {c, d}) :
    (∃ r : Ranking ι n, c ∈ (ofRanking con r candidates).optimal) ↔ ¬ (con · d) < (con · c) := by
  rw [← Pi.forall_toLex_comp_lt_iff hn, not_forall]
  exact exists_congr fun _ ↦ mem_optimal_iff_pair hcand

/-- A candidate is the sole winner against its only competitor under some ranking iff some
constraint prefers it. -/
theorem exists_ofRanking_optimal_eq_singleton_iff_pair (hcand : candidates = {c, d})
    (hne : c ≠ d) :
    (∃ r : Ranking ι n, (ofRanking con r candidates).optimal = {c}) ↔ ∃ i, con i c < con i d := by
  rw [← Pi.exists_toLex_comp_lt_iff hn]
  exact exists_congr fun _ ↦ optimal_eq_singleton_iff_pair hcand hne

end Bounding

end Constructors

/-! ### Evaluation constraint by constraint

Prince and Smolensky's Eval proceeds constraint by constraint: the winners of a tableau are the
winners under its lower constraints among the candidates that do best on its top one, and a
constraint that every candidate violates equally removes no candidate. -/

section Cascade

/-- The candidates doing best on the top constraint of `t`, evaluated by the constraints below
it. -/
def tail (t : Tableau C (n + 1)) : Tableau C n :=
  ⟨t.candidates.argmin (t.constraints 0), Fin.tail t.constraints⟩

/-- The winners of a tableau are the winners of its tail. -/
theorem optimal_tail (t : Tableau C (n + 1)) : t.tail.optimal = t.optimal := by
  ext c
  simp only [mem_optimal_iff, tail, Finset.mem_argmin, profile, Pi.toLex_le_toLex_iff_succ]
  refine ⟨fun ⟨⟨hc, hmin⟩, htail⟩ ↦ ⟨hc, fun d hd ↦ ?_⟩, fun h ↦ ⟨⟨h.1, fun d hd ↦ ?_⟩,
    fun d hd ↦ ?_⟩⟩
  · exact (hmin d hd).lt_or_eq.imp id fun h0 ↦ ⟨h0, htail d ⟨hd, fun e he ↦ h0 ▸ hmin e he⟩⟩
  · rcases h.2 d hd with h0 | ⟨h0, -⟩
    exacts [h0.le, h0.le]
  · rcases h.2 d hd.1 with h0 | ⟨-, ht⟩
    exacts [absurd (hd.2 c h.1) (not_le.2 h0), ht]

variable {s : Finset C} {F : Constraint C} {Fs Gs : List (Constraint C)}

theorem ofList_cons_tail : (ofList s (F :: Fs)).tail = ofList (s.argmin F) Fs := rfl

/-- The winners under a ranked list are the winners under its lower constraints among the
candidates doing best on its top constraint. -/
theorem optimal_ofList_cons : (ofList s (F :: Fs)).optimal = (ofList (s.argmin F) Fs).optimal := by
  rw [← ofList_cons_tail, optimal_tail]

@[simp] theorem optimal_ofList_nil : (ofList s []).optimal = s :=
  Finset.argmin_eq_self_of_forall_le fun _ _ _ _ ↦
    le_of_eq <| funext fun i ↦ absurd i.2 (Nat.not_lt_zero _)

theorem optimal_ofList_cons_of_forall_eq (h : ∀ c ∈ s, ∀ d ∈ s, F c = F d) :
    (ofList s (F :: Fs)).optimal = (ofList s Fs).optimal := by
  rw [optimal_ofList_cons, Finset.argmin_eq_self_of_forall_le fun c hc d hd ↦ (h c hc d hd).le]

/-- Constraints that rate every candidate alike, ranked above the others, do not change the
winners. -/
theorem optimal_ofList_append_of_forall_eq (h : ∀ F ∈ Fs, ∀ c ∈ s, ∀ d ∈ s, F c = F d) :
    (ofList s (Fs ++ Gs)).optimal = (ofList s Gs).optimal := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih =>
    rw [List.cons_append, optimal_ofList_cons_of_forall_eq (h F List.mem_cons_self),
      ih fun F' hF' ↦ h F' (List.mem_cons_of_mem _ hF')]

/-! ### Anti-faithfulness -/

theorem _root_.OptimalityTheory.Constraint.argmin_antifaithful (h : ∃ c ∈ s, 0 < F c) :
    s.argmin F.antifaithful = s.filter (0 < F ·) := by
  obtain ⟨d, hd, hFd⟩ := h
  ext c
  simp only [Finset.mem_argmin, Finset.mem_filter]
  refine ⟨fun ⟨hc, hmin⟩ ↦ ⟨hc, ?_⟩, fun ⟨hc, hFc⟩ ↦ ⟨hc, fun _ _ ↦ ?_⟩⟩
  · have := hmin d hd
    rw [(Constraint.antifaithful_eq_zero_iff F d).2 hFd, Nat.le_zero] at this
    exact (Constraint.antifaithful_eq_zero_iff F c).1 this
  · rw [(Constraint.antifaithful_eq_zero_iff F c).2 hFc]
    exact Nat.zero_le _

theorem optimal_ofList_antifaithful_cons (h : ∃ c ∈ s, 0 < F c) :
    (ofList s (F.antifaithful :: Fs)).optimal = (ofList (s.filter (0 < F ·)) Fs).optimal := by
  rw [optimal_ofList_cons, Constraint.argmin_antifaithful h]

/-- Under `¬F ≫ F`, the winners are the candidates that violate `F` least among those violating
it at all, so that Alderete's anti-faithfulness constraint ranked above `F` forces a minimal
violation of `F`. -/
theorem optimal_ofList_antifaithful (h : ∃ c ∈ s, 0 < F c) :
    (ofList s [F.antifaithful, F]).optimal = (s.filter (0 < F ·)).argmin F := by
  rw [optimal_ofList_antifaithful_cons h, optimal_ofList_cons, optimal_ofList_nil]

end Cascade

section Fintype

variable [Fintype C] {L : Type*} (order : List L) (marks : C → L → ℕ)

/-- The tableau of a printed table: `order` lists the constraint labels in column order, most
dominant first, `marks c l` is the cell of candidate `c` under label `l`, and every inhabitant
of `C` is a candidate. -/
def ofOrder : Tableau C order.length := ⟨Finset.univ, fun p c ↦ marks c (order.get p)⟩

@[simp] theorem ofOrder_candidates : (ofOrder order marks).candidates = Finset.univ := rfl

@[simp] theorem ofOrder_constraints (p : Fin order.length) (c : C) :
    (ofOrder order marks).constraints p c = marks c (order.get p) := rfl

end Fintype

end Tableau

end OptimalityTheory
