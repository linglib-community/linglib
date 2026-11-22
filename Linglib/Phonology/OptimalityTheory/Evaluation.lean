module

public import Linglib.Phonology.OptimalityTheory.Filtration
public import Linglib.Phonology.OptimalityTheory.Ranking.Basic
public import Linglib.Phonology.OptimalityTheory.ViolationProfile
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Evaluation under a ranking

Under a ranking, a candidate's marks are read in rank order and compared lexicographically: the
optimal candidates are those of least profile, the *harmonic ordering of forms* of
[prince-smolensky-1993]. The marks are given by a tableau `T`, with `T c` the marks of the
candidate `c`, and the candidates by a finite set.

Profiles are compared as the violation vectors are in the lexicographic order of the constraints
under dominance (`OptimalityTheory.Ranking.Enumeration.profile_lt_iff_lex`), so one candidate
[beats](##OptimalityTheory.Ranking.Enumeration.profile_lt_iff_exists_dominates)
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

variable {C ι : Type*} {n : ℕ} (σ : Ranking.Enumeration ι n) (T : Tableau C ι) (s : Finset C)
  {c d : C}

/-- The profile of a candidate: its marks in rank order, compared lexicographically. -/
def profile (c : C) : ViolationProfile n := toLex fun p ↦ T c (σ p)

@[simp] theorem profile_apply (c : C) (p : Fin n) : σ.profile T c p = T c (σ p) := rfl

/-- The optimal candidates under a ranking: those of least profile. -/
def optimal : Finset C := s.argmin (σ.profile T)

variable {σ T s}

theorem mem_optimal_iff :
    c ∈ σ.optimal T s ↔ c ∈ s ∧ ∀ d ∈ s, σ.profile T c ≤ σ.profile T d :=
  Finset.mem_argmin

theorem optimal_subset : σ.optimal T s ⊆ s := Finset.argmin_subset ..

theorem optimal_nonempty (h : s.Nonempty) : (σ.optimal T s).Nonempty :=
  Finset.argmin_nonempty h

private theorem optimal_eq_singleton_iff' :
    σ.optimal T s = {c} ↔ c ∈ s ∧ ∀ d ∈ s, d ≠ c → σ.profile T c < σ.profile T d :=
  Finset.argmin_eq_singleton_iff

/-- The optimal candidates are the survivors of filtration along the ranking. -/
theorem optimal_eq_filtration : σ.optimal T s = filtration T s (List.ofFn σ) := by
  ext c
  rw [mem_optimal_iff, mem_filtration]
  refine and_congr_right fun _ ↦ forall₂_congr fun d _ ↦ ?_
  rw [List.map_ofFn, List.map_ofFn, List.ofFn_le_ofFn_iff]
  rfl

/-- Profiles under a ranking are compared as the violation vectors are in the lexicographic order
of the constraints under dominance. -/
theorem profile_lt_iff_lex :
    σ.profile T c < σ.profile T d ↔ Pi.Lex σ.Dominates (· < ·) (T c) (T d) :=
  Pi.toLex_comp_lt_toLex_comp_iff σ

/-- One candidate beats another iff some constraint preferring it dominates every constraint
preferring the other. -/
theorem profile_lt_iff_exists_dominates :
    σ.profile T c < σ.profile T d ↔
      ∃ i, T c i < T d i ∧ ∀ j, T d j < T c j → σ.Dominates i j :=
  profile_lt_iff_lex.trans Pi.lex_iff_exists_forall

/-- The winners depend only on how a ranking orders the constraints that tell the candidates
apart: for an injection `f` of constraints, some ranking of its domain orders it as `σ` orders its
image, and has the winners of `σ` on any candidates that agree on every constraint outside the
image. -/
theorem exists_optimal_comp {κ : Type*} [Fintype κ] (σ : Ranking.Enumeration ι n)
    (f : κ → ι) (hf : Function.Injective f) :
    ∃ τ : Ranking κ, (∀ a b, τ.Dominates a b ↔ σ.Dominates (f a) (f b)) ∧
      ∀ (T : Tableau C ι) (s : Finset C),
        (∀ c ∈ s, ∀ d ∈ s, ∀ i, (∀ a, f a ≠ i) → T c i = T d i) →
          τ.optimal (fun c a ↦ T c (f a)) s = σ.optimal T s := by
  obtain ⟨τ, hτ⟩ := exists_dominates_iff (fun a ↦ σ.symm (f a)) (σ.symm.injective.comp hf) rfl
  refine ⟨τ, hτ, fun T s h ↦ ?_⟩
  ext c
  simp only [mem_optimal_iff, ← not_lt, profile_lt_iff_exists_dominates]
  refine and_congr_right fun hc ↦ forall₂_congr fun d hd ↦ not_congr ⟨?_, ?_⟩
  · rintro ⟨a, h1, h2⟩
    refine ⟨f a, h1, fun j hj ↦ ?_⟩
    obtain ⟨b, rfl⟩ : ∃ b, f b = j := by_contra fun hj' ↦
      hj.ne (h c hc d hd j (not_exists.1 hj'))
    exact (hτ a b).1 (h2 b hj)
  · rintro ⟨i, h1, h2⟩
    obtain ⟨a, rfl⟩ : ∃ a, f a = i := by_contra fun hi ↦
      h1.ne (h d hd c hc i (not_exists.1 hi))
    exact ⟨a, h1, fun b hb ↦ (hτ a b).2 (h2 (f b) hb)⟩

/-- A candidate that violates every constraint at most as often as another, and some constraint
less often, beats it under every ranking. -/
theorem profile_lt_of_lt (h : T c < T d) : σ.profile T c < σ.profile T d :=
  profile_lt_iff_lex.2 (Pi.lex_lt_of_lt (InvImage.wf _ wellFounded_lt) h)

/-- A candidate is the sole winner iff it is a candidate and, against each competitor, some
constraint preferring it dominates every constraint preferring the competitor. -/
theorem optimal_eq_singleton_iff :
    σ.optimal T s = {c} ↔ c ∈ s ∧ ∀ d ∈ s, d ≠ c →
      ∃ i, T c i < T d i ∧ ∀ j, T d j < T c j → σ.Dominates i j :=
  optimal_eq_singleton_iff'.trans <| and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦
    imp_congr_right fun _ ↦ profile_lt_iff_exists_dominates

/-- Ties do not depend on the ranking: beside a winner, the winners are the candidates with the
same violations. -/
theorem mem_optimal_iff_of_mem (hc : c ∈ σ.optimal T s) :
    d ∈ σ.optimal T s ↔ d ∈ s ∧ T d = T c := by
  constructor
  · intro hd
    refine ⟨optimal_subset hd, funext fun i ↦ ?_⟩
    have h := le_antisymm ((mem_optimal_iff.1 hd).2 c (optimal_subset hc))
      ((mem_optimal_iff.1 hc).2 d (optimal_subset hd))
    simpa using congrFun (congrArg ofLex h) (σ.symm i)
  · rintro ⟨hd, h⟩
    have he : σ.profile T d = σ.profile T c := congrArg toLex (funext fun p ↦ congrFun h (σ p))
    exact mem_optimal_iff.2 ⟨hd, fun e he' ↦ he ▸ (mem_optimal_iff.1 hc).2 e he'⟩

/-- A winner is the sole winner iff no other candidate has the same violations. -/
theorem optimal_eq_singleton_iff_of_mem (hc : c ∈ σ.optimal T s) :
    σ.optimal T s = {c} ↔ ∀ d ∈ s, T d = T c → d = c := by
  refine ⟨fun h d hd he ↦ ?_, fun h ↦ Finset.eq_singleton_iff_unique_mem.2 ⟨hc, fun d hd ↦ ?_⟩⟩
  · exact Finset.mem_singleton.1 (h ▸ (mem_optimal_iff_of_mem hc).2 ⟨hd, he⟩)
  · exact h d (optimal_subset hd) ((mem_optimal_iff_of_mem hc).1 hd).2

/-- A candidate is the sole winner under every ranking that extends a relation `R` on the
constraints, such as the Hasse diagram an analysis prints, if against each competitor some
constraint preferring it is `R`-above every constraint preferring the competitor. -/
theorem optimal_eq_singleton_of_rel {R : ι → ι → Prop} (hr : R ≤ σ.Dominates) (hc : c ∈ s)
    (h : ∀ d ∈ s, d ≠ c → ∃ i, T c i < T d i ∧ ∀ j, T d j < T c j → R i j) :
    σ.optimal T s = {c} :=
  optimal_eq_singleton_iff.2 ⟨hc, fun d hd hne ↦
    (h d hd hne).imp fun i ⟨hi, hj⟩ ↦ ⟨hi, fun j hjd ↦ hr i j (hj j hjd)⟩⟩

/-- A candidate that violates every constraint at least as often as a competitor, and some
constraint more often, is *harmonically bounded*: it is optimal under no ranking. -/
theorem notMem_optimal_of_lt (hc : c ∈ s) (hlt : T c < T d) : d ∉ σ.optimal T s :=
  fun hd ↦ ((mem_optimal_iff.1 hd).2 c hc).not_gt (profile_lt_of_lt hlt)

theorem optimal_eq_singleton_of_forall_lt (hc : c ∈ s) (hlt : ∀ d ∈ s, d ≠ c → T c < T d) :
    σ.optimal T s = {c} :=
  optimal_eq_singleton_iff'.2 ⟨hc, fun d hd hne ↦ profile_lt_of_lt (hlt d hd hne)⟩

/-- A candidate with no violations wins under every ranking. -/
theorem zero_mem_optimal (hc : c ∈ s) (hzero : T c = 0) : c ∈ σ.optimal T s :=
  mem_optimal_iff.2 ⟨hc, fun d _ ↦ by
    rw [show σ.profile T c = 0 from congrArg toLex (funext fun p ↦ congrFun hzero (σ p))]
    exact bot_le⟩

/-- If some candidate satisfies every constraint, then under every ranking so does every
winner. -/
theorem eq_zero_of_mem_optimal (hc : c ∈ σ.optimal T s) (hd : d ∈ s) (h0 : T d = 0) :
    T c = 0 := by
  have hp : σ.profile T c = 0 :=
    le_antisymm (by
      rw [← show σ.profile T d = 0 from congrArg toLex (funext fun p ↦ congrFun h0 (σ p))]
      exact (mem_optimal_iff.1 hc).2 d hd) bot_le
  have h2 : (fun p ↦ T c (σ p)) = 0 := congrArg ofLex hp
  exact funext fun i ↦ by simpa using congrFun h2 (σ.symm i)

/-- If the constraints `U` dominate all the others, a candidate satisfying all of `U` beats a
candidate violating any of them. -/
theorem profile_lt_of_forall_dominates {U : Set ι} (hU : ∀ i ∈ U, ∀ j ∉ U, σ.Dominates i j)
    (hc : ∀ i ∈ U, T c i = 0) {i : ι} (hi : i ∈ U) (hd : T d i ≠ 0) :
    σ.profile T c < σ.profile T d := by
  refine profile_lt_iff_exists_dominates.2
    ⟨i, by rw [hc i hi]; omega, fun j hj ↦ hU i hi j fun hjU ↦ ?_⟩
  simp [hc j hjU] at hj

/-- Optimality transfers along constraint-wise bounds: a candidate `d` of a second candidate set
that violates each constraint no more than a winner `c` of the first is itself a winner, provided
every candidate of the second set violates each constraint at least as much as some candidate of
the first. -/
theorem mem_optimal_of_forall_le {C' : Type*} {T' : Tableau C' ι} {s' : Finset C'} {d : C'}
    (hc : c ∈ σ.optimal T s) (hd : d ∈ s') (hdc : T' d ≤ T c)
    (h : ∀ d' ∈ s', ∃ c' ∈ s, T c' ≤ T' d') : d ∈ σ.optimal T' s' := by
  have hm {a b : ι → ℕ} (h : a ≤ b) : toLex (a ∘ σ) ≤ toLex (b ∘ σ) :=
    Pi.toLex_monotone fun p ↦ h (σ p)
  refine mem_optimal_iff.2 ⟨hd, fun d' hd' ↦ ?_⟩
  obtain ⟨c', hc', hle⟩ := h d' hd'
  exact (hm hdc).trans (((mem_optimal_iff.1 hc).2 c' hc').trans (hm hle))

/-- Against its only competitor a candidate is the sole winner iff its profile is less. -/
theorem optimal_eq_singleton_iff_pair [DecidableEq C] (hs : s = {c, d}) (hne : c ≠ d) :
    σ.optimal T s = {c} ↔ σ.profile T c < σ.profile T d := by
  simp [optimal_eq_singleton_iff', hs, hne.symm]

/-- Against its only competitor a candidate wins iff its profile is not greater. -/
theorem mem_optimal_iff_pair [DecidableEq C] (hs : s = {c, d}) :
    c ∈ σ.optimal T s ↔ ¬ σ.profile T d < σ.profile T c := by
  simp [mem_optimal_iff, hs]

/-- Two candidates with no other competitor both win iff no constraint tells them apart. -/
theorem optimal_eq_pair_iff [DecidableEq C] (hs : s = {c, d}) :
    σ.optimal T s = {c, d} ↔ T c = T d := by
  subst hs
  have base : σ.optimal T {c, d} = {c, d} ↔ σ.profile T c = σ.profile T d := by
    refine ⟨fun h ↦ ?_, fun h ↦ optimal_subset.antisymm fun e he ↦ ?_⟩
    · exact le_antisymm
        ((mem_optimal_iff.1 (h.symm ▸ (by simp : c ∈ ({c, d} : Finset C)))).2 d (by simp))
        ((mem_optimal_iff.1 (h.symm ▸ (by simp : d ∈ ({c, d} : Finset C)))).2 c (by simp))
    · have hle : ∀ x ∈ ({c, d} : Finset C), ∀ y ∈ ({c, d} : Finset C),
          σ.profile T x ≤ σ.profile T y := by simp [h]
      exact mem_optimal_iff.2 ⟨he, fun y hy ↦ hle e he y hy⟩
  rw [base]
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ congrArg toLex (funext fun p ↦ congrFun h (σ p))⟩
  simpa using congrFun (congrArg ofLex h) (σ.symm i)

/-- If some candidate violates none of the constraints a ranking puts above its last, the winners
are the candidates violating none of them that do best on the last. -/
theorem optimal_eq_argmin_filter [Fintype ι] [DecidableEq ι] {σ : Ranking.Enumeration ι (n + 1)}
    (h : ∃ c ∈ s, ∀ i ≠ σ (Fin.last n), T c i = 0) :
    σ.optimal T s =
      (s.filter fun c ↦ ∀ i ≠ σ (Fin.last n), T c i = 0).argmin (T · (σ (Fin.last n))) := by
  set j := σ (Fin.last n)
  have hr : ∀ i ≠ j, σ.Dominates i j := fun i hi ↦ by
    rw [Ranking.Enumeration.Dominates, Equiv.symm_apply_apply, Fin.lt_last_iff_ne_last]
    exact fun h ↦ hi (σ.symm_apply_eq.1 h)
  obtain ⟨m, hm, hm0⟩ := h
  ext c
  simp only [mem_optimal_iff, ← not_lt, profile_lt_iff_exists_dominates, Finset.mem_argmin,
    Finset.mem_filter, and_imp]
  constructor
  · rintro ⟨hc, hopt⟩
    have hc0 : ∀ i ≠ j, T c i = 0 := fun i hi ↦ by
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
    by_cases hd0 : ∀ k ≠ j, T d k = 0
    · exact hmin d hd hd0 hi
    · push Not at hd0
      obtain ⟨k, hk, hpos⟩ := hd0
      exact asymm (hdom k (by rw [hc0 k hk]; omega)) (hr k hk)

section Bounding

variable [DecidableEq C] [Fintype ι] (hn : Fintype.card ι = n)
include hn

omit [DecidableEq C] in
/-- One candidate beats another under some ranking iff some constraint prefers it. -/
theorem exists_profile_lt_iff :
    (∃ σ : Ranking.Enumeration ι n, σ.profile T c < σ.profile T d) ↔ ∃ i, T c i < T d i := by
  refine ⟨fun ⟨σ, h⟩ ↦ ?_, fun ⟨i, hi⟩ ↦ ?_⟩
  · obtain ⟨i, hi, -⟩ := profile_lt_iff_exists_dominates.1 h
    exact ⟨i, hi⟩
  · obtain ⟨σ, hσ⟩ := Ranking.Enumeration.exists_forall_dominates i hn
    exact ⟨σ, profile_lt_iff_exists_dominates.2
      ⟨i, hi, fun j hj ↦ hσ j fun hji ↦ (hji ▸ hj).asymm hi⟩⟩

omit [DecidableEq C] in
/-- One candidate beats another under every ranking iff it harmonically bounds it: its violations
are below the other's in the product order. -/
theorem forall_profile_lt_iff :
    (∀ σ : Ranking.Enumeration ι n, σ.profile T c < σ.profile T d) ↔ T c < T d := by
  refine ⟨fun h ↦ Pi.lt_def.2 ⟨fun i ↦ not_lt.1 fun hi ↦ ?_, ?_⟩, fun h σ ↦ profile_lt_of_lt h⟩
  · obtain ⟨σ, hσ⟩ := (exists_profile_lt_iff hn).2 ⟨i, hi⟩
    exact (h σ).asymm hσ
  · exact (exists_profile_lt_iff hn).1 ⟨_, h (Fintype.equivFinOfCardEq hn).symm⟩

/-- A candidate wins against its only competitor under some ranking iff the competitor does not
harmonically bound it. -/
theorem exists_mem_optimal_iff_pair (hs : s = {c, d}) :
    (∃ σ : Ranking.Enumeration ι n, c ∈ σ.optimal T s) ↔ ¬ T d < T c := by
  rw [← forall_profile_lt_iff hn (T := T) (c := d) (d := c), not_forall]
  exact exists_congr fun σ ↦ mem_optimal_iff_pair hs

/-- A candidate is the sole winner against its only competitor under some ranking iff some
constraint prefers it. -/
theorem exists_optimal_eq_singleton_iff_pair (hs : s = {c, d}) (hne : c ≠ d) :
    (∃ σ : Ranking.Enumeration ι n, σ.optimal T s = {c}) ↔ ∃ i, T c i < T d i := by
  rw [← exists_profile_lt_iff hn (T := T) (c := c) (d := d)]
  exact exists_congr fun σ ↦ optimal_eq_singleton_iff_pair hs hne

omit [DecidableEq C] in
/-- Among candidates that violate each constraint at most once, a candidate wins under some
ranking iff no candidate's violations are a proper part of its own. -/
theorem exists_mem_optimal_iff_minimalFor (h : ∀ d ∈ s, ∀ i, T d i ≤ 1) :
    (∃ σ : Ranking.Enumeration ι n, c ∈ σ.optimal T s) ↔ MinimalFor (· ∈ s) T c := by
  refine ⟨fun ⟨σ, hσ⟩ ↦ ⟨optimal_subset hσ, fun d hd hle ↦ by_contra fun hnle ↦ ?_⟩, fun hc ↦ ?_⟩
  · exact notMem_optimal_of_lt hd (lt_of_le_not_ge hle hnle) hσ
  · obtain ⟨σ, hσ⟩ := Ranking.Enumeration.exists_dominates_iff
      (fun i ↦ toLex (T c i, Fintype.equivFinOfCardEq hn i))
      (fun i j hij ↦ (Fintype.equivFinOfCardEq hn).injective (Prod.ext_iff.1 hij).2) hn
    refine ⟨σ, mem_optimal_iff.2 ⟨hc.prop, fun d hd ↦ not_lt.1 fun hlt ↦ ?_⟩⟩
    obtain ⟨i, hi, hdom⟩ := profile_lt_iff_exists_dominates.1 hlt
    obtain ⟨j, hj⟩ : ∃ j, T c j < T d j := by
      by_contra hno
      exact (hc.le_of_le hd fun j ↦ not_lt.1 fun hj ↦ hno ⟨j, hj⟩) i |>.not_gt hi
    have hij : T c i ≤ T c j :=
      (Prod.Lex.toLex_lt_toLex.1 ((hσ i j).1 (hdom j hj))).elim le_of_lt fun h ↦ h.1.le
    have := h d hd j
    omega

end Bounding

end OptimalityTheory.Ranking.Enumeration

namespace OptimalityTheory.Constraint

/-- Eval along a list of constraints is lexicographic minimization of the profiles along it. -/
theorem eval_eq_argmin_ofList {C : Type*} {s : Finset C} {Fs : List (Constraint C)} :
    eval s Fs = s.argmin (ViolationProfile.ofList Fs) := by
  ext c
  rw [mem_eval, Finset.mem_argmin]
  refine and_congr_right fun _ ↦ forall₂_congr fun d _ ↦ ?_
  have key : ∀ x : C, Fs.map (· x) = List.ofFn fun p ↦ Fs.get p x := fun x ↦ by
    conv_lhs => rw [← List.ofFn_get Fs]
    rw [List.map_ofFn]
    rfl
  rw [key, key, List.ofFn_le_ofFn_iff]
  rfl

end OptimalityTheory.Constraint
