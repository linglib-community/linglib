/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.Subsequential.MyhillNerode

/-!
# The Myhill–Nerode theorem for Mealy machines

A function `f : List α → List β` is Mealy-computable if and only if it preserves length and
prefixes and has finitely many residuals (`isMealyComputable_iff_residual`). The residual of the
run of a machine by `u` is the run from the state reached on `u` (`Mealy.residual_run`).

## References

* [S. Eilenberg, *Automata, Languages and Machines, Volume A* (1974)][eilenberg-1974]
* [W. M. L. Holcombe, *Algebraic Automata Theory* (1982)][holcombe-1982]
-/

@[expose] public section

open Function

variable {α β : Type*}

/-- A length-preserving function whose output at each position is given by `c` on the input
before, at and after the position is determined by `c`. -/
theorem getElem?_eq_of_append_cons {f : List α → List β}
    (hlen : ∀ xs, (f xs).length = xs.length) {c : List α → α → List α → β}
    (hc : ∀ u x w, (f (u ++ x :: w))[u.length]? = some (c u x w)) (xs : List α) (i : ℕ) :
    (f xs)[i]? = xs[i]?.map fun a ↦ c (xs.take i) a (xs.drop (i + 1)) := by
  rcases lt_or_ge i xs.length with hi | hi
  · have key := hc (xs.take i) xs[i] (xs.drop (i + 1))
    rw [List.length_take_of_le hi.le, ← List.drop_eq_getElem_cons hi,
      List.take_append_drop] at key
    rw [key, List.getElem?_eq_getElem hi, Option.map_some]
  · rw [List.getElem?_eq_none ((hlen xs).le.trans hi), List.getElem?_eq_none hi,
      Option.map_none]

theorem Mealy.residual_run {σ : Type*} (T : Mealy σ α β) (u : List α) :
    T.run.residual u = T.runFrom (T.eval u) := by
  rw [residual_eq_of_forall (P := T.runFrom T.start u) (v := [])
    (g := T.runFrom (T.eval u)) fun w ↦ by
      rw [List.nil_append]; exact T.runFrom_append T.start u w]
  exact residual_nil rfl

theorem IsMealyComputable.length_eq {f : List α → List β} (hf : IsMealyComputable f)
    (xs : List α) : (f xs).length = xs.length := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.length_run xs

theorem IsMealyComputable.isPrefix {f : List α → List β} (hf : IsMealyComputable f)
    (u v : List α) : f u <+: f (u ++ v) := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact ⟨_, (T.runFrom_append T.start u v).symm⟩

theorem IsMealyComputable.finite_range_residual {f : List α → List β}
    (hf : IsMealyComputable f) : (Set.range f.residual).Finite :=
  hf.isLeftSubsequential.finite_range_residual

/-- A length-preserving `f` with a finite `state : List α → σ` that is left-congruent
(`hδ`) and determines `f`'s output at each position (`hout`) is Mealy-computable. -/
theorem isMealyComputable_of_stateSummary
    {f : List α → List β} {σ : Type*} [Fintype σ]
    (state : List α → σ) (δ : σ → α → σ) (out : σ → α → β)
    (hδ : ∀ u x, state (u ++ [x]) = δ (state u) x)
    (hout : ∀ u x w, (f (u ++ x :: w))[u.length]? = some (out (state u) x))
    (hlen : ∀ xs, (f xs).length = xs.length) :
    IsMealyComputable f := by
  set T : Mealy σ α β := ⟨state [], δ, out⟩
  suffices T.run = f from this ▸ T.isMealyComputable
  have hstate : ∀ u, T.eval u = state u := foldl_eq_of_append_singleton hδ []
  funext xs
  refine List.ext_getElem? fun i ↦ ?_
  rw [T.getElem?_run, getElem?_eq_of_append_cons hlen hout, hstate]

theorem isMealyComputable_of_residual {f : List α → List β}
    (hlen : ∀ xs, (f xs).length = xs.length)
    (hpre : ∀ u v, f u <+: f (u ++ v))
    (hfin : (Set.range f.residual).Finite) :
    IsMealyComputable f := by
  have := Set.Finite.fintype hfin
  have hne : ∀ (r : Set.range f.residual) (x : α), r.val [x] ≠ [] := by
    rintro ⟨_, u, rfl⟩ x
    exact List.ne_nil_of_length_pos (by simp [residual_eq_drop (hpre u), hlen])
  refine isMealyComputable_of_stateSummary
    (fun u ↦ ⟨f.residual u, Set.mem_range_self u⟩)
    (fun r x ↦ ⟨r.val.residual [x], by
      obtain ⟨u, hu⟩ := r.prop
      exact ⟨u ++ [x], by rw [residual_append, hu]⟩⟩)
    (fun r x ↦ (r.val [x]).head (hne r x))
    (fun u x ↦ Subtype.ext (residual_append u [x]))
    (fun u x w ↦ ?_) hlen
  obtain ⟨t, ht⟩ := hpre (u ++ [x]) w
  rw [List.append_assoc, List.singleton_append] at ht
  rw [← ht, List.getElem?_append_left (by rw [hlen]; simp), ← List.head?_drop, ← hlen u,
    show (f (u ++ [x])).drop (f u).length = f.residual u [x] by rw [residual_eq_drop (hpre u)],
    List.head?_eq_some_head]

/-- A function is Mealy-computable iff it is length-preserving, prefix-preserving, and has finitely
many residuals, which is the Myhill–Nerode theorem for Mealy machines. -/
theorem isMealyComputable_iff_residual {f : List α → List β} :
    IsMealyComputable f
      ↔ (∀ xs, (f xs).length = xs.length) ∧ (∀ u v, f u <+: f (u ++ v))
        ∧ (Set.range f.residual).Finite :=
  ⟨fun hf ↦ ⟨hf.length_eq, hf.isPrefix, hf.finite_range_residual⟩,
   fun h ↦ isMealyComputable_of_residual h.1 h.2.1 h.2.2⟩
