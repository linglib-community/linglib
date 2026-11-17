module

public import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Filtration

Optimality-theoretic evaluation is filtration: the candidates are passed through the constraints
one at a time, most dominant first, and each constraint keeps the candidates that violate it
least. The [filtration](##OptimalityTheory.filtration) of a candidate set along a list of
constraints is defined for any list, so it evaluates the prefix of a ranking, a ranking of some of
the constraints, or a whole ranking alike. Its survivors are
[the candidates whose violations along the list are lexicographically
least](##OptimalityTheory.mem_filtration), and along a whole ranking they are
[the winners of the tableau](##OptimalityTheory.Tableau.optimal_ofRanking_eq_filtration).
Filtration never empties a non-empty candidate set, a longer list keeps a subset of what its
prefix keeps, and the survivors agree on every constraint of the list. A candidate that some
ranking selects and that survives a prefix
[is selected by a completion of the prefix](##OptimalityTheory.mem_filtration_append_filter).

## References

* [prince-smolensky-1993]
* [merchant-prince-2022]
-/

@[expose] public section

namespace OptimalityTheory

variable {C ι : Type*} {v : C → ι → ℕ} {s : Finset C} {l l₁ l₂ : List ι} {c d : C} {k : ι}

/-- The filtration of the candidates `s` along a list of constraints, most dominant first: each
constraint in turn keeps the candidates that violate it least. `v c k` is the number of violations
of the constraint `k` by the candidate `c`. -/
def filtration (v : C → ι → ℕ) (s : Finset C) : List ι → Finset C
  | [] => s
  | k :: l => filtration v (s.argmin (v · k)) l

@[simp] theorem filtration_nil : filtration v s [] = s := rfl

@[simp] theorem filtration_cons :
    filtration v s (k :: l) = filtration v (s.argmin (v · k)) l := rfl

/-- Filtration along a concatenation filters along the first list and then along the second. -/
theorem filtration_append :
    filtration v s (l₁ ++ l₂) = filtration v (filtration v s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons k l ih => exact ih

/-- The survivors of filtration are the candidates whose violations along the list are
lexicographically least. -/
theorem mem_filtration :
    c ∈ filtration v s l ↔ c ∈ s ∧ ∀ d ∈ s, l.map (v c) ≤ l.map (v d) := by
  induction l generalizing s with
  | nil => simp
  | cons k l ih =>
    simp only [filtration_cons, ih, Finset.mem_argmin, List.map_cons, List.cons_le_cons_iff']
    constructor
    · rintro ⟨⟨hc, hk⟩, h⟩
      refine ⟨hc, fun d hd ↦ ?_⟩
      rcases (hk d hd).lt_or_eq with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, h d ⟨hd, fun b hb ↦ heq ▸ hk b hb⟩⟩
    · rintro ⟨hc, h⟩
      have hk : ∀ b ∈ s, v c k ≤ v b k := fun b hb ↦ (h b hb).elim le_of_lt fun h ↦ h.1.le
      refine ⟨⟨hc, hk⟩, fun d hd ↦ ?_⟩
      rcases h d hd.1 with hlt | ⟨-, hle⟩
      · exact absurd (hd.2 c hc) (not_le.2 hlt)
      · exact hle

theorem filtration_subset : filtration v s l ⊆ s := fun _ h ↦ (mem_filtration.1 h).1

/-- Telescoping: a longer list keeps a subset of what its prefix keeps. -/
theorem filtration_append_subset : filtration v s (l₁ ++ l₂) ⊆ filtration v s l₁ := by
  rw [filtration_append]
  exact filtration_subset

/-- Forced choice: filtration never empties a non-empty candidate set. -/
theorem filtration_nonempty (h : s.Nonempty) : (filtration v s l).Nonempty := by
  induction l generalizing s with
  | nil => exact h
  | cons k l ih => exact ih (Finset.argmin_nonempty h)

/-- Survivor sameness: the survivors agree on every constraint of the list. -/
theorem apply_eq_of_mem_filtration (hc : c ∈ filtration v s l) (hd : d ∈ filtration v s l)
    (hk : k ∈ l) : v c k = v d k := by
  have h₁ := (mem_filtration.1 hc).2 d (mem_filtration.1 hd).1
  have h₂ := (mem_filtration.1 hd).2 c (mem_filtration.1 hc).1
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hk
  have h := congrArg (fun x ↦ x[i]?) (le_antisymm h₁ h₂)
  simpa [List.getElem?_map, List.getElem?_eq_getElem hi] using h

/-- A constraint on which the candidates all agree filters nothing. -/
theorem filtration_cons_of_forall_eq (h : ∀ a ∈ s, ∀ b ∈ s, v a k = v b k) :
    filtration v s (k :: l) = filtration v s l := by
  rw [filtration_cons, Finset.argmin_eq_self_of_forall_le fun a ha b hb ↦ (h a ha b hb).le]

/-- Dropping the constraints on which two candidates agree does not change which of them does
better along a list. -/
theorem map_filter_le_map_filter_iff {p : ι → Prop} [DecidablePred p]
    (h : ∀ k ∈ l, ¬ p k → v c k = v d k) :
    (l.filter p).map (v c) ≤ (l.filter p).map (v d) ↔ l.map (v c) ≤ l.map (v d) := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    have ih := ih fun k hk ↦ h k (List.mem_cons_of_mem _ hk)
    by_cases hk : p k
    · rw [List.filter_cons_of_pos (by simp [hk])]
      simp only [List.map_cons, List.cons_le_cons_iff', ih]
    · have he := h k List.mem_cons_self hk
      rw [List.filter_cons_of_neg (by simp [hk])]
      simp only [List.map_cons, List.cons_le_cons_iff', ih, he, lt_irrefl, true_and, false_or]

/-- A candidate is the sole survivor iff its violations along the list are lexicographically
least, strictly. -/
theorem filtration_eq_singleton_iff :
    filtration v s l = {c} ↔ c ∈ s ∧ ∀ d ∈ s, d ≠ c → l.map (v c) < l.map (v d) := by
  refine ⟨fun h ↦ ?_, fun ⟨hc, h⟩ ↦ ?_⟩
  · have hc : c ∈ filtration v s l := h ▸ Finset.mem_singleton_self c
    refine ⟨filtration_subset hc, fun d hd hne ↦ ?_⟩
    have hd' : d ∉ filtration v s l := h ▸ fun hd' ↦ hne (Finset.mem_singleton.1 hd')
    rw [mem_filtration, not_and, not_forall₂] at hd'
    obtain ⟨e, he, hlt⟩ := hd' hd
    exact ((mem_filtration.1 hc).2 e he).trans_lt (not_le.1 hlt)
  · have hc' : c ∈ filtration v s l := mem_filtration.2 ⟨hc, fun d hd ↦ by
      rcases eq_or_ne d c with rfl | hne
      exacts [le_rfl, (h d hd hne).le]⟩
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨hc', fun d hd ↦ by_contra fun hne ↦ ?_⟩
    exact ((mem_filtration.1 hd).2 c hc).not_gt (h d (filtration_subset hd) hne)

/-- A candidate that violates each constraint of the list at least as often as a competitor,
and one of them more often, does not survive: it is harmonically bounded. -/
theorem notMem_filtration_of_forall_le (hc : c ∈ s) (hle : ∀ k ∈ l, v c k ≤ v d k)
    (hlt : ∃ k ∈ l, v c k < v d k) : d ∉ filtration v s l := by
  induction l generalizing s with
  | nil => simp at hlt
  | cons k l ih =>
    rw [filtration_cons]
    intro hd
    have hdk := Finset.mem_argmin.1 (filtration_subset hd)
    have hck : v c k = v d k := le_antisymm (hle k List.mem_cons_self) (hdk.2 c hc)
    refine ih (Finset.mem_argmin.2 ⟨hc, fun b hb ↦ hck ▸ hdk.2 b hb⟩)
      (fun j hj ↦ hle j (List.mem_cons_of_mem _ hj)) ?_ hd
    obtain ⟨j, hj, hjlt⟩ := hlt
    rcases List.mem_cons.1 hj with rfl | hj
    · exact absurd hjlt hck.not_lt
    · exact ⟨j, hj, hjlt⟩

/-- No Dead Man Walking ([merchant-prince-2022]): a candidate that survives filtration along
a list `l`, such as a whole ranking, and also along a list `l₁`, survives along `l₁` followed
by the constraints of `l` that are not in `l₁`. A possible optimum that passes a prefix is
selected by some completion of the prefix. -/
theorem mem_filtration_append_filter [DecidableEq ι] (hl : c ∈ filtration v s l)
    (hl₁ : c ∈ filtration v s l₁) : c ∈ filtration v s (l₁ ++ l.filter (· ∉ l₁)) := by
  rw [filtration_append, mem_filtration]
  refine ⟨hl₁, fun d hd ↦ ?_⟩
  rw [map_filter_le_map_filter_iff fun k _ hk ↦
    apply_eq_of_mem_filtration hl₁ hd (not_not.1 hk)]
  exact (mem_filtration.1 hl).2 d (filtration_subset hd)

variable {n : ℕ}

/-- The winners of a tableau under a ranking are the survivors of filtration along the
ranking. -/
theorem Tableau.optimal_ofRanking_eq_filtration (con : ConstraintSet C ι)
    (r : Ranking.Enumeration ι n)
    (s : Finset C) :
    (Tableau.ofRanking con r s).optimal = filtration (fun c k ↦ con k c) s (List.ofFn r) := by
  ext c
  rw [Tableau.mem_optimal_iff, mem_filtration]
  refine and_congr_right fun _ ↦ forall₂_congr fun d _ ↦ ?_
  rw [List.map_ofFn, List.map_ofFn, List.ofFn_le_ofFn_iff]
  rfl

/-! ### Evaluation along a list of constraints -/

section Eval

variable {F : Constraint C} {Fs Gs : List (Constraint C)}

/-- Eval: the candidates of `s` that are optimal under the constraints `Fs`, most dominant first.
It is filtration with each constraint counting its own violations. -/
def Constraint.eval (s : Finset C) (Fs : List (Constraint C)) : Finset C :=
  filtration Function.eval s Fs

@[simp] theorem Constraint.eval_nil : Constraint.eval s [] = s := rfl

theorem Constraint.eval_cons :
    Constraint.eval s (F :: Fs) = Constraint.eval (s.argmin F) Fs := rfl

theorem Constraint.eval_append :
    Constraint.eval s (Fs ++ Gs) = Constraint.eval (Constraint.eval s Fs) Gs :=
  filtration_append

theorem Constraint.eval_subset : Constraint.eval s Fs ⊆ s := filtration_subset

theorem Constraint.eval_nonempty (hs : s.Nonempty) : (Constraint.eval s Fs).Nonempty :=
  filtration_nonempty hs

@[simp] theorem Constraint.eval_singleton : Constraint.eval {c} Fs = {c} :=
  Finset.Subset.antisymm eval_subset <| Finset.singleton_subset_iff.2 <| by
    obtain ⟨d, hd⟩ := eval_nonempty (Fs := Fs) (Finset.singleton_nonempty c)
    exact Finset.mem_singleton.1 (eval_subset hd) ▸ hd

/-- A candidate that does strictly best on the most dominant constraint is the sole winner. -/
theorem Constraint.eval_cons_eq_singleton (hc : c ∈ s) (h : ∀ d ∈ s, d ≠ c → F c < F d) :
    Constraint.eval s (F :: Fs) = {c} := by
  rw [eval_cons, Finset.argmin_eq_singleton_iff.2 ⟨hc, h⟩, eval_singleton]

/-- A candidate is optimal under the constraints iff its violations along the list are
lexicographically at most every candidate's. -/
theorem Constraint.mem_eval :
    c ∈ Constraint.eval s Fs ↔ c ∈ s ∧ ∀ d ∈ s, Fs.map (· c) ≤ Fs.map (· d) :=
  mem_filtration

/-- A candidate is the sole winner iff its violations along the list are lexicographically
strictly below every other candidate's. -/
theorem Constraint.eval_eq_singleton_iff :
    Constraint.eval s Fs = {c} ↔ c ∈ s ∧ ∀ d ∈ s, d ≠ c → Fs.map (· c) < Fs.map (· d) :=
  filtration_eq_singleton_iff

theorem Constraint.eval_cons_of_forall_eq (h : ∀ c ∈ s, ∀ d ∈ s, F c = F d) :
    Constraint.eval s (F :: Fs) = Constraint.eval s Fs := by
  rw [eval_cons, Finset.argmin_eq_self_of_forall_le fun c hc d hd ↦ (h c hc d hd).le]

/-- Constraints that rate every candidate alike, ranked above the others, do not change the
winners. -/
theorem Constraint.eval_append_of_forall_eq (h : ∀ F ∈ Fs, ∀ c ∈ s, ∀ d ∈ s, F c = F d) :
    Constraint.eval s (Fs ++ Gs) = Constraint.eval s Gs := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih =>
    rw [List.cons_append, eval_cons_of_forall_eq (h F List.mem_cons_self),
      ih fun F' hF' ↦ h F' (List.mem_cons_of_mem _ hF')]

/-- If some candidate satisfies every constraint ranked above the others, so does every
winner. -/
theorem Constraint.eq_zero_of_mem_eval_append (hc : c ∈ Constraint.eval s (Fs ++ Gs))
    (hd : d ∈ s) (h0 : ∀ F ∈ Fs, F d = 0) : ∀ F ∈ Fs, F c = 0 := by
  induction Fs generalizing s with
  | nil => simp
  | cons F Fs ih =>
    rw [List.cons_append, eval_cons] at hc
    have hF : F d = 0 := h0 F List.mem_cons_self
    refine List.forall_mem_cons.2
      ⟨Nat.le_zero.1 (hF ▸ (Finset.mem_argmin.1 (eval_subset hc)).2 d hd), ih hc ?_
        fun F' hF' ↦ h0 F' (List.mem_cons_of_mem _ hF')⟩
    exact Finset.mem_argmin.2 ⟨hd, fun _ _ ↦ hF ▸ Nat.zero_le _⟩

/-- A candidate that violates each constraint at least as often as a competitor, and one of
them more often, is not optimal. -/
theorem Constraint.notMem_eval_of_forall_le (hc : c ∈ s) (hle : ∀ F ∈ Fs, F c ≤ F d)
    (hlt : ∃ F ∈ Fs, F c < F d) : d ∉ Constraint.eval s Fs :=
  notMem_filtration_of_forall_le hc hle hlt

theorem Constraint.eval_antifaithful_cons (h : ∃ c ∈ s, 0 < F c) :
    Constraint.eval s (F.antifaithful :: Fs) = Constraint.eval (s.filter (0 < F ·)) Fs := by
  rw [eval_cons, Constraint.argmin_antifaithful h]

/-- Under `¬F ≫ F`, the winners are the candidates that violate `F` least among those violating
it at all. -/
theorem Constraint.eval_antifaithful (h : ∃ c ∈ s, 0 < F c) :
    Constraint.eval s [F.antifaithful, F] = (s.filter (0 < F ·)).argmin F := by
  rw [eval_antifaithful_cons h, eval_cons, eval_nil]

/-- The winners of the tableau of a list of constraints are the candidates Eval keeps. -/
theorem Tableau.optimal_ofList (s : Finset C) (Fs : List (Constraint C)) :
    (Tableau.ofList s Fs).optimal = Constraint.eval s Fs := by
  induction Fs generalizing s with
  | nil => exact Tableau.optimal_ofList_nil
  | cons F Fs ih => rw [Tableau.optimal_ofList_cons, ih, Constraint.eval_cons]

/-! ### Candidates named by labels -/

variable {L : Type*} {cand : L → C} {labels : Finset L} {x : L}

/-- Eval over candidates named by labels: the labels in `labels` whose candidates, `cand l` for
the label `l`, are optimal under the constraints `Fs`. -/
def Constraint.evalOn (cand : L → C) (labels : Finset L) (Fs : List (Constraint C)) : Finset L :=
  Constraint.eval labels (Fs.map (Constraint.comap cand))

theorem Constraint.evalOn_append :
    Constraint.evalOn cand labels (Fs ++ Gs) =
      Constraint.evalOn cand (Constraint.evalOn cand labels Fs) Gs := by
  rw [evalOn, List.map_append, eval_append]
  rfl

theorem Constraint.evalOn_cons_eq_singleton (hx : x ∈ labels)
    (h : ∀ y ∈ labels, y ≠ x → F (cand x) < F (cand y)) :
    Constraint.evalOn cand labels (F :: Fs) = {x} :=
  eval_cons_eq_singleton hx h

theorem Tableau.optimal_ofLabels (cand : L → C) (labels : Finset L) (Fs : List (Constraint C)) :
    (Tableau.ofLabels cand labels Fs).optimal = Constraint.evalOn cand labels Fs :=
  Tableau.optimal_ofList _ _

end Eval

end OptimalityTheory
