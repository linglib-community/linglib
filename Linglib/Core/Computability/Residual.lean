/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: transducer sections of `Mathlib.Computability.MyhillNerode`, with
`Function.residual` beside `Language.leftQuotient`.
-/
module

public import Mathlib.Basic.Finite.Set
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Fintype.Option
public import Mathlib.Order.Lattice.Nat
public import Linglib.Core.Computability.Mealy
public import Linglib.Core.Computability.Bimachine
public import Linglib.Core.Computability.Subsequential

/-!
# Residuals of string functions

This file characterizes the subsequential, Mealy-computable and bimachine-computable functions by
their residuals, in the style of the Myhill–Nerode theorem for languages. The *prefix function* of
`f : List α → List β` sends a word `u` to the longest common prefix of the outputs of `f` on the
extensions of `u`, and the *residual* of `f` by `u` sends `v` to what `f` outputs on `u ++ v`
beyond that prefix. Residuals compose as a right action of words,
and a function is subsequential if and only if it has finitely many residuals, the
characterization of Oncina and García recalled by Chandlee, Eyraud and Heinz. A subsequential
function is Mealy-computable exactly when it is also length- and prefix-preserving, the Nerode
criterion of Eilenberg and Holcombe.

A length-preserving function whose output at a position can depend on input unboundedly far to
its right, as in bidirectional harmony, has infinitely many residuals in this sense. Such
functions are characterized instead by their *synchronous* residuals and coresiduals, which cut
the output where the input is cut: a length-preserving function is bimachine-computable if and
only if it has finitely many of each, the length-preserving stratum
of the canonical bimachine of Reutenauer and Schützenberger surveyed by Filiot and Reynier.

## Main definitions

* `Function.prefixFunction f u`: the longest common prefix of `f` on the extensions of `u`
* `Function.residual f u`: the residual of `f` by the word `u`
* `Function.syncResidual f u`, `Function.syncCoresidual f y`: the output after `u` and before `y`
  of a length-preserving `f`

## Main results

* `Function.residual_append`: residuals compose as a right action of words
* `isLeftSubsequential_iff_finite_range_residual`: `f` is left-subsequential if and only if it
  has finitely many residuals
* `isMealyComputable_iff_residual`: `f` is Mealy-computable if and only if it is length- and
  prefix-preserving with finitely many residuals
* `isLengthPreservingBimachineComputable_iff_syncResidual`: a length-preserving `f` is
  bimachine-computable if and only if it has finitely many synchronous residuals and coresiduals

## Implementation notes

The prefix function takes the supremum in `ℕ` of the lengths of the common prefixes, so it and
the residual are noncomputable. For a prefix-preserving `f` the prefix function is `f` itself
(`prefixFunction_eq_self`) and the residual drops `f u` (`residual_eq_drop`), which on
length-preserving functions is the synchronous residual (`residual_eq_syncResidual`).

## References

* [S. Eilenberg, *Automata, Languages and Machines, Volume A* (1974)][eilenberg-1974]
* [W. M. L. Holcombe, *Algebraic Automata Theory* (1982)][holcombe-1982]
* [C. Reutenauer and M. P. Schützenberger, *Minimization of Rational Word Functions*
  (1991)][reutenauer-schutzenberger-1991]
* [E. Filiot and P. A. Reynier, *Transducers, Logic and Algebra for Functions of Finite Words*
  (2016)][filiot-reynier-2016]
* [J. Chandlee, R. Eyraud and J. Heinz, *Output Strictly Local Functions*
  (2015)][chandlee-eyraud-heinz-2015]
-/

@[expose] public section

variable {α β : Type*} (f : List α → List β)

namespace Function

/-! ### The prefix function and residuals -/

/-- The **prefix function** of `f` sends `u` to the longest common prefix of the outputs of `f`
on the extensions of `u`, the output already determined after reading `u`. -/
noncomputable def prefixFunction (u : List α) : List β :=
  (f u).take (sSup {n | n ≤ (f u).length ∧ ∀ w, (f u).take n <+: f (u ++ w)})

/-- The **residual** of `f` by `u` sends `v` to what `f` outputs on `u ++ v` beyond the prefix
function at `u`, the analogue for string functions of `Language.leftQuotient`. -/
noncomputable def residual (u : List α) : List α → List β :=
  fun v ↦ (f (u ++ v)).drop (f.prefixFunction u).length

variable {f} {g : List α → List β} {u v : List α} {p : List β}

private lemma bddAbove_commonPrefixLengths :
    BddAbove {n | n ≤ (f u).length ∧ ∀ w, (f u).take n <+: f (u ++ w)} :=
  ⟨_, fun _ h ↦ h.1⟩

private lemma sSup_mem_commonPrefixLengths :
    sSup {n | n ≤ (f u).length ∧ ∀ w, (f u).take n <+: f (u ++ w)} ∈
      {n | n ≤ (f u).length ∧ ∀ w, (f u).take n <+: f (u ++ w)} :=
  Nat.sSup_mem ⟨0, Nat.zero_le _, fun w ↦ by simp⟩ bddAbove_commonPrefixLengths

theorem prefixFunction_prefix (u w : List α) : f.prefixFunction u <+: f (u ++ w) :=
  sSup_mem_commonPrefixLengths.2 w

/-- The prefix function at `u` is the greatest common prefix of `f` on the extensions of
`u`. -/
theorem prefix_prefixFunction_iff : p <+: f.prefixFunction u ↔ ∀ w, p <+: f (u ++ w) := by
  refine ⟨fun h w ↦ h.trans (prefixFunction_prefix u w), fun h ↦ ?_⟩
  have hu : p <+: f u := by simpa using h []
  have hp : p = (f u).take p.length := List.prefix_iff_eq_take.mp hu
  exact List.prefix_take_iff.mpr ⟨hu, le_csSup bddAbove_commonPrefixLengths
    ⟨hu.length_le, fun w ↦ hp ▸ h w⟩⟩

theorem prefixFunction_eq_self (h : ∀ w, f u <+: f (u ++ w)) : f.prefixFunction u = f u :=
  ((prefix_prefixFunction_iff.mpr h).eq_of_length_le
    (by simpa using (prefixFunction_prefix (f := f) u []).length_le)).symm

theorem prefixFunction_append_residual (u v : List α) :
    f.prefixFunction u ++ f.residual u v = f (u ++ v) := by
  obtain ⟨t, ht⟩ := prefixFunction_prefix (f := f) u v
  simp [residual, ← ht]

/-- A function prefix-preserving at `u` extends its output on `u` by the residual. -/
theorem append_residual (h : ∀ w, f u <+: f (u ++ w)) (v : List α) :
    f u ++ f.residual u v = f (u ++ v) :=
  prefixFunction_eq_self h ▸ prefixFunction_append_residual u v

theorem residual_eq_drop (h : ∀ w, f u <+: f (u ++ w)) :
    f.residual u = fun v ↦ (f (u ++ v)).drop (f u).length := by
  rw [← prefixFunction_eq_self h]
  rfl

theorem residual_nil (h : f [] = []) : f.residual [] = f := by
  rw [residual_eq_drop (u := []) fun w ↦ by simp [h]]
  funext v
  simp [h]

/-- If `f` on the extensions of `u` is `P` followed by `g` on the extensions of `v`, then its
prefix function at `u` is `P` followed by that of `g` at `v`. -/
theorem prefixFunction_eq_of_forall {P : List β} (h : ∀ w, f (u ++ w) = P ++ g (v ++ w)) :
    f.prefixFunction u = P ++ g.prefixFunction v := by
  have hP : P <+: f.prefixFunction u := prefix_prefixFunction_iff.mpr fun w ↦ h w ▸
    List.prefix_append _ _
  obtain ⟨r, hr⟩ := hP
  refine (List.IsPrefix.eq_of_length ?_ ?_).symm
  · exact prefix_prefixFunction_iff.mpr fun w ↦ h w ▸ (List.prefix_append_right_inj P).mpr
      (prefixFunction_prefix v w)
  · have : r <+: g.prefixFunction v := prefix_prefixFunction_iff.mpr fun w ↦
      (List.prefix_append_right_inj P).mp (h w ▸ hr ▸ prefixFunction_prefix u w)
    have := this.length_le
    have := (prefix_prefixFunction_iff.mpr fun w ↦ h w ▸ (List.prefix_append_right_inj P).mpr
      (prefixFunction_prefix (f := g) v w)).length_le
    simp only [← hr, List.length_append] at *
    omega

theorem residual_eq_of_forall {P : List β} (h : ∀ w, f (u ++ w) = P ++ g (v ++ w)) :
    f.residual u = g.residual v := by
  funext w
  rw [residual, residual, h, prefixFunction_eq_of_forall h, List.length_append,
    List.drop_append]
  simp

/-- Residuals compose as a right action of words, the residual by `u ++ v` being the residual by
`v` of the residual by `u`. -/
theorem residual_append (u v : List α) : f.residual (u ++ v) = (f.residual u).residual v :=
  residual_eq_of_forall fun w ↦ by
    rw [List.append_assoc]
    exact (prefixFunction_append_residual u (v ++ w)).symm

end Function

/-! ### Residuals through a state summary

A function that extends its output by one block per letter, the block read off a summary `W`
of the input whose update is determined, has residuals that factor through `W`; conversely a
prefix-preserving function whose residuals factor through `W` extends by blocks read off `W`.
The strictly local function classes are the instances with `W` a bounded window. -/

namespace Function

section StateSummary

variable {f} {γ : Type*} {W : List α → γ}

/-- A function extending its output at every letter is prefix-preserving. -/
theorem isPrefix_append_of_append_singleton (hf : ∀ u x, f u <+: f (u ++ [x])) (u v : List α) :
    f u <+: f (u ++ v) := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v x ih => exact ih.trans (List.append_assoc u v [x] ▸ hf (u ++ v) x)

/-- Residuals of a function built block by block from a state summary factor through it. -/
theorem factorsThrough_residual_of_append_singleton (δ : γ → α → γ) (g : γ → α → List β)
    (hW : ∀ u x, W (u ++ [x]) = δ (W u) x) (hf : ∀ u x, f (u ++ [x]) = f u ++ g (W u) x) :
    f.residual.FactorsThrough W := by
  have hpre := isPrefix_append_of_append_singleton fun u x ↦ ⟨_, (hf u x).symm⟩
  intro u₁ u₂ h
  rw [residual_eq_drop (hpre u₁), residual_eq_drop (hpre u₂)]
  funext v
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v x ih =>
    have hWv : W (u₁ ++ v) = W (u₂ ++ v) := by
      clear ih
      induction v using List.reverseRecOn with
      | nil => simpa using h
      | append_singleton v y ihv => rw [← List.append_assoc, hW, ihv, ← hW, List.append_assoc]
    rw [← List.append_assoc, hf, List.drop_append_of_le_length (hpre u₁ v).length_le, ih,
      ← List.append_assoc, hf, List.drop_append_of_le_length (hpre u₂ v).length_le, hWv]

/-- A prefix-preserving function whose residuals factor through `W` extends by blocks read
off `W`. -/
theorem exists_append_singleton_of_factorsThrough_residual
    (hpre : ∀ u v, f u <+: f (u ++ v)) (hW : f.residual.FactorsThrough W) :
    ∃ g : γ → α → List β, ∀ u x, f (u ++ [x]) = f u ++ g (W u) x :=
  ⟨fun c x ↦ Function.extend W f.residual (fun _ _ ↦ []) c [x], fun u x ↦ by
    dsimp only
    rw [hW.extend_apply, append_residual (hpre u) [x]]⟩

end StateSummary

end Function

open Function

/-! ### Myhill–Nerode for subsequential transducers -/

section Subsequential

variable {f}

/-- Residuals of a transducer's run factor through its states. -/
theorem SubsequentialTransducer.residual_run {σ : Type*} (T : SubsequentialTransducer σ α β)
    (u : List α) : T.run.residual u = (T.runFrom (T.stateAfter T.start u)).residual [] :=
  residual_eq_of_forall (P := T.emitted T.start u) fun w ↦ by
    rw [List.nil_append]; exact T.run_append u w

theorem IsLeftSubsequential.finite_range_residual (hf : IsLeftSubsequential f) :
    (Set.range f.residual).Finite := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact (Set.finite_range fun q ↦ (T.runFrom q).residual []).subset
    (Set.range_subset_iff.mpr fun u ↦ ⟨_, (T.residual_run u).symm⟩)

/-- A function with finitely many residuals is left-subsequential. The residuals are the states,
each emitting its prefix function on the next letter and its value on `[]` at the end, and a
fresh start state reads the first letter off `f` itself. -/
theorem IsLeftSubsequential.of_finite_range_residual (hf : (Set.range f.residual).Finite) :
    IsLeftSubsequential f := by
  have := hf.fintype
  let fn : Option (Set.range f.residual) → List α → List β := fun q ↦ q.elim f Subtype.val
  have hstep : ∀ q x, (fn q).residual [x] ∈ Set.range f.residual := by
    rintro (_ | ⟨_, u, rfl⟩) x
    · exact ⟨[x], rfl⟩
    · exact ⟨u ++ [x], residual_append u [x]⟩
  let T : SubsequentialTransducer (Option (Set.range f.residual)) α β :=
    { start := none
      step := fun q x ↦ some ⟨_, hstep q x⟩
      output := fun q x ↦ (fn q).prefixFunction [x]
      finalOutput := fun q ↦ fn q [] }
  have hrun : ∀ q v, T.runFrom q v = fn q v := by
    intro q v
    induction v generalizing q with
    | nil => rfl
    | cons x v ih =>
      rw [SubsequentialTransducer.runFrom_cons, ih]
      exact prefixFunction_append_residual [x] v
  have hT : T.run = f := funext fun v ↦ hrun none v
  exact hT ▸ T.isLeftSubsequential

/-- **Myhill–Nerode for subsequential transducers.** A function is left-subsequential if and
only if it has finitely many residuals ([chandlee-eyraud-heinz-2015], after Oncina and
García). -/
theorem isLeftSubsequential_iff_finite_range_residual :
    IsLeftSubsequential f ↔ (Set.range f.residual).Finite :=
  ⟨IsLeftSubsequential.finite_range_residual, IsLeftSubsequential.of_finite_range_residual⟩

/-- A function is right-subsequential if and only if its reverse-conjugate has finitely many
residuals. -/
theorem isRightSubsequential_iff_finite_range_residual :
    IsRightSubsequential f ↔ (Set.range (List.revConj f).residual).Finite :=
  isLeftSubsequential_iff_finite_range_residual

end Subsequential

/-! ### Myhill–Nerode for Mealy machines -/

/-- Residuals of a machine's run are its runs from the states it reaches. -/
theorem Mealy.residual_run {σ : Type*} (T : Mealy σ α β) (u : List α) :
    T.run.residual u = T.runFrom (T.stateAfter T.start u) := by
  rw [residual_eq_of_forall (P := T.runFrom T.start u) (v := [])
    (g := T.runFrom (T.stateAfter T.start u)) fun w ↦ by
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
  have hstate : ∀ ps : List α, T.stateAfter T.start ps = state ps := by
    intro ps
    induction ps using List.reverseRecOn with
    | nil => rfl
    | append_singleton ps x ih => rw [T.stateAfter_append, ih, hδ]; rfl
  funext xs
  apply List.ext_getElem?
  intro i
  rw [T.getElem?_run xs i, hstate]
  rcases lt_or_ge i xs.length with hi | hi
  · have key := hout (xs.take i) xs[i] (xs.drop (i + 1))
    rw [List.length_take_of_le hi.le, ← List.drop_eq_getElem_cons hi,
      List.take_append_drop] at key
    rw [List.getElem?_eq_getElem hi, Option.map_some, key]
  · rw [List.getElem?_eq_none hi, List.getElem?_eq_none ((hlen xs).le.trans hi),
      Option.map_none]

/-- A length-preserving, prefix-preserving function with finitely many residuals is
Mealy-computable, with the residuals themselves as the states. -/
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

/-- **Myhill–Nerode for Mealy machines.** A function is Mealy-computable if and only
if it is length-preserving, prefix-preserving, and has finitely many residuals. -/
theorem isMealyComputable_iff_residual {f : List α → List β} :
    IsMealyComputable f
      ↔ (∀ xs, (f xs).length = xs.length) ∧ (∀ u v, f u <+: f (u ++ v))
        ∧ (Set.range f.residual).Finite :=
  ⟨fun hf ↦ ⟨hf.length_eq, hf.isPrefix, hf.finite_range_residual⟩,
   fun h ↦ isMealyComputable_of_residual h.1 h.2.1 h.2.2⟩

/-! ### Synchronous residuals and coresiduals -/

namespace Function

/-- The **synchronous residual** of `f` by `u` is the output of `f` on `u ++ v` past the first
`u.length` symbols, the cells after `u` of a length-preserving `f`. -/
def syncResidual (u : List α) : List α → List β :=
  fun v ↦ (f (u ++ v)).drop u.length

/-- The **synchronous coresidual** of `f` by `y` is the output of `f` on `u ++ y` up to its
first `u.length` symbols, the cells before `y` of a length-preserving `f`. -/
def syncCoresidual (y : List α) : List α → List β :=
  fun u ↦ (f (u ++ y)).take u.length

theorem syncResidual_append_singleton (u : List α) (x : α) :
    syncResidual f (u ++ [x]) = fun v ↦ (syncResidual f u (x :: v)).drop 1 := by
  funext v; simp [syncResidual]

/-- Synchronous coresiduals step by prepending a letter, the right-to-left congruence. -/
theorem syncCoresidual_cons (x : α) (y : List α) :
    syncCoresidual f (x :: y) = fun u ↦ (syncCoresidual f y (u ++ [x])).take u.length := by
  funext u
  simp only [syncCoresidual, List.take_take, List.length_append, List.length_cons,
    List.length_nil, List.append_assoc, List.singleton_append]
  rw [Nat.min_eq_left (Nat.le_succ _)]

/-- The cell at the seam, read through the synchronous residual. -/
theorem getElem?_syncResidual_cons (u : List α) (x : α) (w : List α) :
    (syncResidual f u (x :: w))[0]? = (f (u ++ x :: w))[u.length]? := by
  simp [syncResidual, List.getElem?_drop]

/-- The cell at the seam, read through the synchronous coresidual. -/
theorem getElem?_syncCoresidual_append (u : List α) (x : α) (w : List α) :
    (syncCoresidual f w (u ++ [x]))[u.length]? = (f (u ++ x :: w))[u.length]? := by
  simp only [syncCoresidual, List.length_append, List.length_cons, List.length_nil,
    List.append_assoc, List.singleton_append]
  exact List.getElem?_take_of_lt (Nat.lt_succ_self _)

/-- On a length- and prefix-preserving function the residual is the synchronous residual. -/
theorem residual_eq_syncResidual {f : List α → List β} (hlen : ∀ xs, (f xs).length = xs.length)
    (hpre : ∀ u v, f u <+: f (u ++ v)) : f.residual = f.syncResidual := by
  funext u
  rw [residual_eq_drop (hpre u), hlen]
  rfl

end Function

/-! ### Myhill–Nerode for bimachines -/

section Bimachine

variable {L R : Type*} (B : Bimachine L R α β)

/-- Scanning past a prefix reseeds the left state. -/
theorem Bimachine.lState_append (u v : List α) :
    B.lState (u ++ v) = B.lStateAfter (B.lState u) v := by
  simp [Bimachine.lState, Bimachine.lStateAfter, List.foldl_append]

/-- A pending suffix reseeds the right state. -/
theorem Bimachine.rState_append (u y : List α) :
    B.rState (u ++ y) = Bimachine.rState {B with rInit := B.rState y} u := by
  simp [Bimachine.rState, List.foldr_append]

/-- Dropping a scanned prefix of a letter-to-letter bimachine run reseeds the left
state. -/
theorem Bimachine.drop_runFrom_append (w : B.LetterToLetter) (l : L) (x v : List α) :
    (B.runFrom l (x ++ v)).drop x.length = B.runFrom (B.lStateAfter l x) v := by
  induction x generalizing l with
  | nil => rfl
  | cons a x ih => simpa [w.output_eq] using ih (B.lStep l a)

/-- Taking the unscanned prefix of a bimachine run reseeds the right state. -/
theorem Bimachine.take_runFrom_append (w : B.LetterToLetter) (l : L) (u y : List α) :
    (B.runFrom l (u ++ y)).take u.length
      = Bimachine.runFrom {B with rInit := B.rState y} l u := by
  induction u generalizing l with
  | nil => rfl
  | cons a u ih =>
    rw [List.cons_append, B.runFrom_cons, w.output_eq, List.singleton_append,
      List.length_cons, List.take_succ_cons, ih (B.lStep l a), B.rState_append u y]
    simp [w.output_eq]

/-- Residuals of a bimachine's run reseed the left automaton. -/
theorem Bimachine.syncResidual_run (w : B.LetterToLetter) (x : List α) :
    syncResidual B.run x = B.runFrom (B.lState x) :=
  funext fun v ↦ B.drop_runFrom_append w B.lInit x v

/-- Coresiduals of a bimachine's run reseed the right automaton. -/
theorem Bimachine.syncCoresidual_run (w : B.LetterToLetter) (y : List α) :
    syncCoresidual B.run y = Bimachine.run {B with rInit := B.rState y} :=
  funext fun u ↦ B.take_runFrom_append w B.lInit u y

/-! ### Necessity -/

theorem IsLengthPreservingBimachineComputable.finite_range_syncResidual {f : List α → List β}
    (hf : IsLengthPreservingBimachineComputable f) : (Set.range (syncResidual f)).Finite := by
  obtain ⟨L, _, R, _, B, ⟨w⟩, rfl⟩ := hf
  exact Set.Finite.subset (Set.finite_range B.runFrom)
    (Set.range_subset_iff.mpr fun x ↦ ⟨_, (B.syncResidual_run w x).symm⟩)

theorem IsLengthPreservingBimachineComputable.finite_range_syncCoresidual {f : List α → List β}
    (hf : IsLengthPreservingBimachineComputable f) : (Set.range (syncCoresidual f)).Finite := by
  obtain ⟨L, _, R, _, B, ⟨w⟩, rfl⟩ := hf
  exact Set.Finite.subset (Set.finite_range fun r : R ↦ Bimachine.run {B with rInit := r})
    (Set.range_subset_iff.mpr fun y ↦ ⟨B.rState y, (B.syncCoresidual_run w y).symm⟩)

/-! ### Sufficiency -/

/-- A length-preserving `f` with finite left and right summaries, congruent in their
respective scan directions and jointly determining each output cell, is
bimachine-computable. -/
theorem isLengthPreservingBimachineComputable_of_stateSummaries
    {f : List α → List β} {L R : Type*} [Fintype L] [Fintype R]
    (stateL : List α → L) (δL : L → α → L) (stateR : List α → R) (δR : R → α → R)
    (out : L → α → R → β)
    (hδL : ∀ u x, stateL (u ++ [x]) = δL (stateL u) x)
    (hδR : ∀ x w, stateR (x :: w) = δR (stateR w) x)
    (hout : ∀ u x w, (f (u ++ x :: w))[u.length]? = some (out (stateL u) x (stateR w)))
    (hlen : ∀ xs, (f xs).length = xs.length) :
    IsLengthPreservingBimachineComputable f := by
  set B : Bimachine L R α β := ⟨stateL [], δL, stateR [], δR, fun l a r ↦ [out l a r]⟩
  suffices B.run = f from
    this ▸ B.isLengthPreservingBimachineComputable ⟨⟨out, fun _ _ _ ↦ rfl⟩⟩
  have hL : ∀ ps : List α, B.lState ps = stateL ps := by
    intro ps
    induction ps using List.reverseRecOn with
    | nil => rfl
    | append_singleton ps x ih =>
      rw [B.lState_append, hδL, ← ih]
      rfl
  have hR : ∀ ss : List α, B.rState ss = stateR ss := by
    intro ss
    induction ss with
    | nil => rfl
    | cons x ss ih => rw [B.rState_cons, ih, hδR]
  funext xs
  apply List.ext_getElem?
  intro i
  rw [(⟨out, fun _ _ _ ↦ rfl⟩ : B.LetterToLetter).getElem?_run xs i]
  simp only [hL, hR]
  rcases lt_or_ge i xs.length with hi | hi
  · have key := hout (xs.take i) xs[i] (xs.drop (i + 1))
    rw [List.length_take_of_le hi.le, ← List.drop_eq_getElem_cons hi,
      List.take_append_drop] at key
    rw [List.getElem?_eq_getElem hi, Option.map_some, key]
  · rw [List.getElem?_eq_none hi, List.getElem?_eq_none ((hlen xs).le.trans hi),
      Option.map_none]

/-- A length-preserving function with finitely many residuals and coresiduals is
bimachine-computable, with syncResidual classes as the left states and syncCoresidual classes as the
right states, and with the cell output read off representatives, which is well-defined by
exchanging one context at a time. -/
theorem isLengthPreservingBimachineComputable_of_syncResidual {f : List α → List β}
    (hlen : ∀ xs, (f xs).length = xs.length)
    (hfinL : (Set.range (syncResidual f)).Finite)
    (hfinR : (Set.range (syncCoresidual f)).Finite) :
    IsLengthPreservingBimachineComputable f := by
  have := hfinL.fintype
  have := hfinR.fintype
  choose repL hrepL using fun r : Set.range (syncResidual f) ↦ r.prop
  choose repR hrepR using fun s : Set.range (syncCoresidual f) ↦ s.prop
  refine isLengthPreservingBimachineComputable_of_stateSummaries
    (fun u ↦ ⟨syncResidual f u, Set.mem_range_self u⟩)
    (fun r x ↦ ⟨fun v ↦ (r.val (x :: v)).drop 1, by
      obtain ⟨u, hu⟩ := r.prop
      exact ⟨u ++ [x], by rw [syncResidual_append_singleton f, hu]⟩⟩)
    (fun w ↦ ⟨syncCoresidual f w, Set.mem_range_self w⟩)
    (fun s x ↦ ⟨fun u ↦ (s.val (u ++ [x])).take u.length, by
      obtain ⟨w, hw⟩ := s.prop
      exact ⟨x :: w, by rw [syncCoresidual_cons, hw]⟩⟩)
    (fun r x s ↦ (f (repL r ++ x :: repR s))[(repL r).length]'(by
      rw [hlen]
      simp))
    (fun u x ↦ Subtype.ext (syncResidual_append_singleton f u x))
    (fun x w ↦ Subtype.ext (syncCoresidual_cons f x w))
    (fun u x w ↦ ?_) hlen
  set r : Set.range (syncResidual f) := ⟨syncResidual f u, Set.mem_range_self u⟩
  set s : Set.range (syncCoresidual f) := ⟨syncCoresidual f w, Set.mem_range_self w⟩
  have hres : syncResidual f (repL r) = syncResidual f u := hrepL r
  have hcores : syncCoresidual f (repR s) = syncCoresidual f w := hrepR s
  calc (f (u ++ x :: w))[u.length]?
      = (syncResidual f u (x :: w))[0]? := (getElem?_syncResidual_cons f u x w).symm
    _ = (syncResidual f (repL r) (x :: w))[0]? := by rw [hres]
    _ = (f (repL r ++ x :: w))[(repL r).length]? := getElem?_syncResidual_cons f _ x w
    _ = (syncCoresidual f w (repL r ++ [x]))[(repL r).length]? :=
        (getElem?_syncCoresidual_append f _ x w).symm
    _ = (syncCoresidual f (repR s) (repL r ++ [x]))[(repL r).length]? := by rw [hcores]
    _ = (f (repL r ++ x :: repR s))[(repL r).length]? := getElem?_syncCoresidual_append f _ x _
    _ = some ((f (repL r ++ x :: repR s))[(repL r).length]'(by rw [hlen]; simp)) :=
        List.getElem?_eq_getElem _

end Bimachine

/-- **Myhill–Nerode for bimachines.** A function is bimachine-computable if and only
if it is length-preserving with finitely many residuals and finitely many
coresiduals. -/
theorem isLengthPreservingBimachineComputable_iff_syncResidual {f : List α → List β} :
    IsLengthPreservingBimachineComputable f
      ↔ (∀ xs, (f xs).length = xs.length) ∧ (Set.range (syncResidual f)).Finite
        ∧ (Set.range (syncCoresidual f)).Finite :=
  ⟨fun hf ↦ ⟨hf.length_eq, hf.finite_range_syncResidual, hf.finite_range_syncCoresidual⟩,
   fun h ↦ isLengthPreservingBimachineComputable_of_syncResidual h.1 h.2.1 h.2.2⟩

