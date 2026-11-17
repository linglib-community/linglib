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
prefix keeps, and the survivors agree on every constraint of the list.

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

variable {n : ℕ}

/-- The winners of a tableau under a ranking are the survivors of filtration along the
ranking. -/
theorem Tableau.optimal_ofRanking_eq_filtration (con : ConstraintSet C ι) (r : Ranking ι n)
    (s : Finset C) :
    (Tableau.ofRanking con r s).optimal = filtration (fun c k ↦ con k c) s (List.ofFn r) := by
  ext c
  rw [Tableau.mem_optimal_iff, mem_filtration]
  refine and_congr_right fun _ ↦ forall₂_congr fun d _ ↦ ?_
  rw [List.map_ofFn, List.map_ofFn, List.ofFn_le_ofFn_iff]
  rfl

end OptimalityTheory
