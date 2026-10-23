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

This file characterizes subsequential, Mealy-computable and bimachine-computable functions by
their residuals, in the style of the Myhill–Nerode theorem. The *prefix function* of `f` at `u` is
the longest common prefix of the outputs of `f` on the extensions of `u`, and the *residual* of `f`
by `u` sends `v` to the rest of `f (u ++ v)`. A function is subsequential iff it has finitely many
residuals, and Mealy-computable iff it is moreover length- and prefix-preserving. A
length-preserving function whose output can depend on input unboundedly far to its right, as in
bidirectional harmony, has infinitely many residuals; it is bimachine-computable iff it has
finitely many *synchronous* residuals and coresiduals, which cut the output where the input is cut.

## Main definitions

* `Function.prefixFunction`, `Function.residual`: the prefix function and the residual.
* `Function.syncResidual`, `Function.syncCoresidual`: the output after and before a cut.

## Main results

* `Function.residual_append`: residuals compose as a right action of words.
* `isLeftSubsequential_iff_finite_range_residual`: subsequential iff finitely many residuals.
* `isMealyComputable_iff_residual`: Mealy-computable iff length- and prefix-preserving with
  finitely many residuals.
* `isLengthPreservingBimachineComputable_iff_syncResidual`: a length-preserving `f` is
  bimachine-computable iff it has finitely many synchronous residuals and coresiduals.

## Implementation notes

The prefix function is a supremum in `ℕ`, so it and the residual are noncomputable. For a
prefix-preserving `f` the residual drops `f u` (`residual_eq_drop`), which on length-preserving
functions is the synchronous residual (`residual_eq_syncResidual`).

## References

* [S. Eilenberg, *Automata, Languages and Machines, Volume A* (1974)][eilenberg-1974]: the Nerode
  criterion for Mealy machines, with Holcombe
* [W. M. L. Holcombe, *Algebraic Automata Theory* (1982)][holcombe-1982]
* [C. Reutenauer and M. P. Schützenberger, *Minimization of Rational Word Functions*
  (1991)][reutenauer-schutzenberger-1991]: the canonical bimachine, whose length-preserving
  stratum is the bimachine characterization here
* [E. Filiot and P. A. Reynier, *Transducers, Logic and Algebra for Functions of Finite Words*
  (2016)][filiot-reynier-2016]: a survey of the canonical bimachine
* [J. Chandlee, R. Eyraud and J. Heinz, *Output Strictly Local Functions*
  (2015)][chandlee-eyraud-heinz-2015]: recalls the subsequential characterization of Oncina and
  García
-/

@[expose] public section

variable {α β : Type*} (f : List α → List β)

namespace Function

/-! ### The prefix function and residuals -/

/-- The prefix function of `f` at `u` is the longest common prefix of the outputs of `f` on the
extensions of `u`, that is, the output already determined after reading `u`. -/
noncomputable def prefixFunction (u : List α) : List β :=
  (f u).take (sSup {n | n ≤ (f u).length ∧ ∀ w, (f u).take n <+: f (u ++ w)})

/-- The residual of `f` by `u` sends `v` to what `f` outputs on `u ++ v` beyond the prefix
function at `u`. It is the analogue for string functions of `Language.leftQuotient`. -/
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

/-- The residual by `u ++ v` is the residual by `v` of the residual by `u`, so residuals compose as
a right action of words. -/
theorem residual_append (u v : List α) : f.residual (u ++ v) = (f.residual u).residual v :=
  residual_eq_of_forall fun w ↦ by
    rw [List.append_assoc]
    exact (prefixFunction_append_residual u (v ++ w)).symm

end Function

/-! ### Residuals through a state summary

Let `W` summarize the input, with `W (u ++ [x])` determined by `W u` and `x`. A function whose
output grows by one block per letter, each block determined by the current summary and letter, has
residuals that factor through `W`. Conversely, a prefix-preserving function whose residuals factor
through `W` grows by such blocks. The strictly local function classes are the cases where `W` is a
bounded window. -/

namespace Function

section StateSummary

variable {f} {γ : Type*} {W : List α → γ}

theorem isPrefix_append_of_append_singleton (hf : ∀ u x, f u <+: f (u ++ [x])) (u v : List α) :
    f u <+: f (u ++ v) := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v x ih => exact ih.trans (List.append_assoc u v [x] ▸ hf (u ++ v) x)

theorem foldl_eq_of_append_singleton {δ : γ → α → γ} (hW : ∀ u x, W (u ++ [x]) = δ (W u) x)
    (u v : List α) : v.foldl δ (W u) = W (u ++ v) := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v x ih => rw [List.foldl_concat, ih, ← hW, List.append_assoc]

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
      rw [← foldl_eq_of_append_singleton hW, ← foldl_eq_of_append_singleton hW, h]
    rw [← List.append_assoc, hf, List.drop_append_of_le_length (hpre u₁ v).length_le, ih,
      ← List.append_assoc, hf, List.drop_append_of_le_length (hpre u₂ v).length_le, hWv]

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

theorem SubsequentialTransducer.residual_run {σ : Type*} (T : SubsequentialTransducer σ α β)
    (u : List α) : T.run.residual u = (T.runFrom (T.eval u)).residual [] :=
  residual_eq_of_forall (P := T.emitted T.start u) fun w ↦ by
    rw [List.nil_append]; exact T.run_append u w

theorem IsLeftSubsequential.finite_range_residual (hf : IsLeftSubsequential f) :
    (Set.range f.residual).Finite := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact (Set.finite_range fun q ↦ (T.runFrom q).residual []).subset
    (Set.range_subset_iff.mpr fun u ↦ ⟨_, (T.residual_run u).symm⟩)

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

/-- A function is left-subsequential iff it has finitely many residuals, which is the Myhill–Nerode
theorem for subsequential transducers ([chandlee-eyraud-heinz-2015], after Oncina and García). -/
theorem isLeftSubsequential_iff_finite_range_residual :
    IsLeftSubsequential f ↔ (Set.range f.residual).Finite :=
  ⟨IsLeftSubsequential.finite_range_residual, IsLeftSubsequential.of_finite_range_residual⟩

theorem isRightSubsequential_iff_finite_range_residual :
    IsRightSubsequential f ↔ (Set.range (List.revConj f).residual).Finite :=
  isLeftSubsequential_iff_finite_range_residual

end Subsequential

private theorem getElem?_eq_of_append_cons {f : List α → List β}
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

/-! ### Myhill–Nerode for Mealy machines -/

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

/-! ### Synchronous residuals and coresiduals -/

namespace Function

/-- The synchronous residual of `f` by `u` sends `v` to the output of `f` on `u ++ v` past its first
`u.length` symbols, which for a length-preserving `f` is the output after `u`. -/
def syncResidual (u : List α) : List α → List β :=
  fun v ↦ (f (u ++ v)).drop u.length

/-- The synchronous coresidual of `f` by `y` sends `u` to the first `u.length` symbols of the output
of `f` on `u ++ y`, which for a length-preserving `f` is the output before `y`. -/
def syncCoresidual (y : List α) : List α → List β :=
  fun u ↦ (f (u ++ y)).take u.length

theorem syncResidual_append_singleton (u : List α) (x : α) :
    syncResidual f (u ++ [x]) = fun v ↦ (syncResidual f u (x :: v)).drop 1 := by
  funext v; simp [syncResidual]

theorem syncCoresidual_cons (x : α) (y : List α) :
    syncCoresidual f (x :: y) = fun u ↦ (syncCoresidual f y (u ++ [x])).take u.length := by
  funext u
  simp only [syncCoresidual, List.take_take, List.length_append, List.length_cons,
    List.length_nil, List.append_assoc, List.singleton_append]
  rw [Nat.min_eq_left (Nat.le_succ _)]

theorem getElem?_syncResidual_cons (u : List α) (x : α) (w : List α) :
    (syncResidual f u (x :: w))[0]? = (f (u ++ x :: w))[u.length]? := by
  simp [syncResidual, List.getElem?_drop]

theorem getElem?_syncCoresidual_append (u : List α) (x : α) (w : List α) :
    (syncCoresidual f w (u ++ [x]))[u.length]? = (f (u ++ x :: w))[u.length]? := by
  simp only [syncCoresidual, List.length_append, List.length_cons, List.length_nil,
    List.append_assoc, List.singleton_append]
  exact List.getElem?_take_of_lt (Nat.lt_succ_self _)

theorem residual_eq_syncResidual {f : List α → List β} (hlen : ∀ xs, (f xs).length = xs.length)
    (hpre : ∀ u v, f u <+: f (u ++ v)) : f.residual = f.syncResidual := by
  funext u
  rw [residual_eq_drop (hpre u), hlen]
  rfl

end Function

/-! ### Myhill–Nerode for bimachines -/

section Bimachine

variable {L R : Type*} (B : Bimachine L R α β)

theorem Bimachine.drop_runFrom_append (w : B.LetterToLetter) (l : L) (x v : List α) :
    (B.runFrom l (x ++ v)).drop x.length = B.runFrom (B.lStateAfter l x) v := by
  induction x generalizing l with
  | nil => rfl
  | cons a x ih => simpa [w.output_eq] using ih (B.lStep l a)

theorem Bimachine.take_runFrom_append (w : B.LetterToLetter) (l : L) (u y : List α) :
    (B.runFrom l (u ++ y)).take u.length
      = Bimachine.runFrom {B with rInit := B.rState y} l u := by
  induction u generalizing l with
  | nil => rfl
  | cons a u ih =>
    rw [List.cons_append, B.runFrom_cons, w.output_eq, List.singleton_append,
      List.length_cons, List.take_succ_cons, ih (B.lStep l a), B.rState_append u y]
    simp [w.output_eq]

theorem Bimachine.syncResidual_run (w : B.LetterToLetter) (x : List α) :
    syncResidual B.run x = B.runFrom (B.lState x) :=
  funext fun v ↦ B.drop_runFrom_append w B.lInit x v

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
  have hL : ∀ u, B.lState u = stateL u := foldl_eq_of_append_singleton hδL []
  have hR : ∀ w, B.rState w = stateR w := fun w ↦ by
    induction w with
    | nil => rfl
    | cons x w ih => rw [B.rState_cons, ih, hδR]
  funext xs
  refine List.ext_getElem? fun i ↦ ?_
  rw [(⟨out, fun _ _ _ ↦ rfl⟩ : B.LetterToLetter).getElem?_run,
    getElem?_eq_of_append_cons hlen hout]
  simp only [hL, hR]

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

/-- A function is length-preserving bimachine-computable iff it is length-preserving with finitely
many synchronous residuals and finitely many coresiduals, which is the Myhill–Nerode theorem for
bimachines. -/
theorem isLengthPreservingBimachineComputable_iff_syncResidual {f : List α → List β} :
    IsLengthPreservingBimachineComputable f
      ↔ (∀ xs, (f xs).length = xs.length) ∧ (Set.range (syncResidual f)).Finite
        ∧ (Set.range (syncCoresidual f)).Finite :=
  ⟨fun hf ↦ ⟨hf.length_eq, hf.finite_range_syncResidual, hf.finite_range_syncCoresidual⟩,
   fun h ↦ isLengthPreservingBimachineComputable_of_syncResidual h.1 h.2.1 h.2.2⟩

