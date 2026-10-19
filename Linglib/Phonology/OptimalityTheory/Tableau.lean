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

An OT tableau ([prince-smolensky-1993]) evaluates a finite candidate set by constraints in rank
order. A candidate's violation profile is its violation vector read in rank order and ordered
lexicographically, `Lex (Fin n → ℕ)` ([riggle-2009b]): the lexicographic order is Optimality
Theory's strict domination, while Harmonic Grammar weights the same vector without ordering it
(`HarmonicGrammar.harmonyScore`). The winners are the candidates of least profile, the
`Finset.argmin` of the profile over the candidates.

## Main definitions

* `ViolationProfile n` — `Lex (Fin n → ℕ)`, a fixed-length violation vector.
* `Tableau C n` — candidates `C` and `n` constraints in rank order, position `0` most dominant.
* `Tableau.profile` — a candidate's violation profile.
* `Tableau.optimal` — the winner set; optimality is plain membership.
* `Tableau.ofRanking` — the tableau of a constraint set `con : ConstraintSet C ι` under a ranking
  `r : Ranking ι n`, whose constraint at rank position `p` is `con (r p)`.
* `Tableau.ofList` — the tableau of a ranked constraint list, list order being priority.
* `Tableau.ofOrder` — a tableau from a constraint *order* (labels, most dominant first) and the
  candidates' violation marks by label: the paper-tableau form.

## Main results

* `Tableau.mem_optimal_iff` / `Tableau.optimal_nonempty` / `Tableau.optimal_eq_singleton_iff` —
  the winner characterization; winners exist; sole winner ⟺ strict domination.
* `Tableau.ofRanking_profile_lt_iff_exists_dominates` — a candidate beats another under a ranking
  iff some constraint preferring it dominates every constraint preferring the other.
* `Tableau.notMem_optimal_of_lt` / `Tableau.ofRanking_notMem_optimal_of_lt` — harmonic bounding:
  a candidate beaten pointwise never wins.
* `Tableau.exists_mem_ofRanking_optimal_iff_pair` — a candidate wins against its only competitor
  under some ranking iff the competitor does not harmonically bound it.
* `Tableau.ofRanking_zero_mem_optimal` / `Tableau.ofRanking_eq_zero_of_mem_optimal` — a candidate
  with no violations wins under every ranking, and then every winner has no violations.
* `Tableau.constraints_zero_le_of_mem_optimal` — a winner does at least as well as every
  candidate on the top constraint.

## References

* [A. Prince and P. Smolensky, *Optimality Theory: Constraint Interaction in Generative Grammar*
  (1993)][prince-smolensky-1993]
* [A. Prince, *Entailed Ranking Arguments* (2002)][prince-2002]
* [J. Riggle, *Violation Semirings in Optimality Theory* (2009)][riggle-2009b]
-/

@[expose] public section

namespace OptimalityTheory

/-- A fixed-length violation profile, the violation vector `Fin n → ℕ` under its lexicographic
order. -/
abbrev ViolationProfile (n : ℕ) := Lex (Fin n → ℕ)

/-- An OT tableau: a finite candidate set and the constraints that evaluate it, in rank order. -/
structure Tableau (C : Type*) (n : ℕ) where
  /-- The candidates. -/
  candidates : Finset C
  /-- The constraint at each rank position, position `0` most dominant. -/
  constraints : ConstraintSet C (Fin n)

namespace Tableau

variable {C : Type*} {n : ℕ} (t : Tableau C n) (c : C)

/-- A candidate's violation profile: its violations read in rank order, ordered
lexicographically. -/
def profile : ViolationProfile n := toLex fun p ↦ t.constraints p c

@[simp] theorem profile_apply (p : Fin n) : t.profile c p = t.constraints p c := rfl

/-- The winning candidates, those of least profile. Optimality is plain membership
`c ∈ t.optimal`, unfolded by `mem_optimal_iff`. -/
def optimal : Finset C := t.candidates.argmin t.profile

variable {t c} {d m : C}

/-- A winner is a candidate whose profile is lexicographically below that of every
candidate. -/
theorem mem_optimal_iff :
    c ∈ t.optimal ↔ c ∈ t.candidates ∧ ∀ d ∈ t.candidates, t.profile c ≤ t.profile d :=
  Finset.mem_argmin

theorem optimal_subset : t.optimal ⊆ t.candidates :=
  Finset.argmin_subset

/-- A tableau with a candidate has a winner. -/
theorem optimal_nonempty (h : t.candidates.Nonempty) : t.optimal.Nonempty :=
  Finset.argmin_nonempty h

/-- A winner's profile bounds every candidate's. -/
theorem le_of_mem_optimal (hc : c ∈ t.optimal) (hd : d ∈ t.candidates) :
    t.profile c ≤ t.profile d :=
  (mem_optimal_iff.1 hc).2 d hd

/-- A tableau has sole winner `m` iff `m` is a candidate that strictly lex-dominates every other
candidate. -/
theorem optimal_eq_singleton_iff :
    t.optimal = {m} ↔ m ∈ t.candidates ∧ ∀ c ∈ t.candidates, c ≠ m → t.profile m < t.profile c :=
  Finset.argmin_eq_singleton_iff

/-- A tableau with a single candidate has it as sole winner. -/
@[simp] theorem optimal_singleton (hc : t.candidates = {c}) : t.optimal = {c} :=
  optimal_eq_singleton_iff.2 ⟨by simp [hc], fun _ hd hdc ↦ absurd (by simpa [hc] using hd) hdc⟩

/-- A candidate strictly lex-dominated by a competitor is no winner. -/
theorem notMem_optimal_of_lt (hc : c ∈ t.candidates) (h : t.profile c < t.profile d) :
    d ∉ t.optimal :=
  fun hd ↦ (le_of_mem_optimal hd hc).not_gt h

/-- A candidate with no violations wins, since `0` is the least profile. -/
theorem mem_optimal_of_profile_eq_zero (hc : c ∈ t.candidates) (h0 : t.profile c = 0) :
    c ∈ t.optimal :=
  mem_optimal_iff.2 ⟨hc, fun _ _ ↦ h0 ▸ bot_le⟩

/-- If some candidate has no violations, neither has any winner. -/
theorem profile_eq_zero_of_mem_optimal (hc : c ∈ t.optimal) (hd : d ∈ t.candidates)
    (h0 : t.profile d = 0) : t.profile c = 0 :=
  le_antisymm (h0 ▸ le_of_mem_optimal hc hd) bot_le

/-- A winner does at least as well as every candidate on the top constraint, so a satisfiable
top constraint is satisfied by every winner. -/
theorem constraints_zero_le_of_mem_optimal {t : Tableau C (n + 1)} (hc : c ∈ t.optimal)
    (hd : d ∈ t.candidates) : t.constraints 0 c ≤ t.constraints 0 d :=
  Pi.apply_le_of_toLex (x := (t.constraints · c)) (le_of_mem_optimal hc hd) fun j hj ↦
    absurd hj (Fin.not_lt_zero j)

section Pair

variable [DecidableEq C]

/-- A two-candidate tableau has sole winner `c` iff `c` strictly lex-dominates `d`. -/
theorem optimal_eq_singleton_iff_pair (hcand : t.candidates = {c, d}) (hne : c ≠ d) :
    t.optimal = {c} ↔ t.profile c < t.profile d := by
  simp [optimal_eq_singleton_iff, hcand, hne.symm]

/-- In a two-candidate tableau, `c` wins iff `d` does not strictly lex-dominate it. -/
theorem mem_optimal_iff_pair (hcand : t.candidates = {c, d}) :
    c ∈ t.optimal ↔ ¬ t.profile d < t.profile c := by
  simp [mem_optimal_iff, hcand]

end Pair

/-! ### Tableau constructors -/

section Constructors

variable {ι : Type*} (con : ConstraintSet C ι) (r : Ranking ι n) (candidates : Finset C)
  (ranking : List (Constraint C))

/-- `ofRanking con r candidates` is the tableau of a constraint set `con : ConstraintSet C ι`
under a ranking `r : Ranking ι n`: rank position `p` reads constraint `r p`, so coordinate `0` of
the lexicographic profile is the most dominant constraint. -/
def ofRanking : Tableau C n := ⟨candidates, con ∘ r⟩

/-- The tableau of a ranked constraint list, list order being priority (position `0` most
dominant): `Tableau.ofRanking` under the identity ranking. Study files use this as
`(Tableau.ofList {.a, .b} [c₁, c₂]).optimal = {.a}`. -/
def ofList : Tableau C ranking.length := ofRanking ranking.get (Equiv.refl _) candidates

@[simp] theorem ofRanking_candidates : (ofRanking con r candidates).candidates = candidates := rfl

@[simp] theorem ofRanking_constraints : (ofRanking con r candidates).constraints = con ∘ r := rfl

@[simp] theorem ofList_candidates : (ofList candidates ranking).candidates = candidates := rfl

@[simp] theorem ofList_constraints : (ofList candidates ranking).constraints = ranking.get := rfl

variable {con r candidates}

/-- Under a ranking, one candidate beats another iff some constraint preferring it dominates
every constraint preferring the other, which is the elementary ranking condition. -/
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

/-- A candidate beaten pointwise on the constraint set by a competitor is harmonically bounded,
that is, optimal under no ranking of the set. -/
theorem ofRanking_notMem_optimal_of_lt (hc : c ∈ candidates) (hlt : (con · c) < (con · d)) :
    d ∉ (ofRanking con r candidates).optimal :=
  notMem_optimal_of_lt hc (Pi.toLex_comp_strictMono r hlt)

/-- A candidate that harmonically bounds every competitor is the sole winner under every
ranking of the constraint set. -/
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

section Fintype

variable [Fintype C] {L : Type*} (order : List L) (marks : C → L → ℕ)

/-- The tableau of a constraint order — labels `L`, most dominant first — and each candidate's
violation marks by label, as a paper's tableau is printed: `order` is its column order and
`marks c l` the cell. Candidates are every inhabitant of `C`. -/
def ofOrder : Tableau C order.length := ⟨Finset.univ, fun p c ↦ marks c (order.get p)⟩

@[simp] theorem ofOrder_candidates : (ofOrder order marks).candidates = Finset.univ := rfl

@[simp] theorem ofOrder_constraints (p : Fin order.length) (c : C) :
    (ofOrder order marks).constraints p c = marks c (order.get p) := rfl

end Fintype

end Tableau

end OptimalityTheory
