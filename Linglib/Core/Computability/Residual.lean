/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: transducer sections of `Mathlib.Computability.MyhillNerode`, with
`Function.residual` beside `Language.leftQuotient`.
-/
module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.List.Infix
public import Mathlib.Logic.Function.Basic

/-!
# Residuals of string functions

For a function `f : List α → List β`, the *prefix function* `f.prefixFunction u` is the longest
common prefix of the outputs of `f` on the extensions of `u`, the output already determined
after reading `u`. The *residual* `f.residual u` sends `v` to the rest of `f (u ++ v)`, so that
`f.prefixFunction u ++ f.residual u v = f (u ++ v)`. Residuals are the analogue for string
functions of the left quotients of a language, and they compose as a right action of words
(`Function.residual_append`).

Let `W` summarize the input, with `W (u ++ [x])` determined by `W u` and `x`. A function that
grows by one block per symbol, each read off the summary, and ends with a final output read off
the summary has residuals that factor through `W`
(`Function.factorsThrough_residual_of_append_final`), and conversely the prefix function of a
function whose residuals factor through `W` grows by such blocks
(`Function.exists_prefixFunction_append_singleton_of_factorsThrough_residual`).

The *synchronous residual* `f.syncResidual u` and *coresidual* `f.syncCoresidual y` cut the
output where the input is cut. On a length- and prefix-preserving function the synchronous
residual is the residual (`Function.residual_eq_syncResidual`).

## Implementation notes

The prefix function is a supremum in `ℕ`, so it and the residual are noncomputable. For a
prefix-preserving `f` the residual drops `f u` (`Function.residual_eq_drop`).

## References

* [J. Chandlee, R. Eyraud and J. Heinz, *Output Strictly Local Functions*
  (2015)][chandlee-eyraud-heinz-2015]
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

theorem prefixFunction_isPrefix (f : List α → List β) (u v : List α) :
    f.prefixFunction u <+: f.prefixFunction (u ++ v) :=
  prefix_prefixFunction_iff.mpr fun w ↦ List.append_assoc u v w ▸ prefixFunction_prefix u (v ++ w)

/-- The prefix function grows on reading `x` by the prefix function of the residual at `[x]`. -/
theorem prefixFunction_append_singleton (f : List α → List β) (u : List α) (x : α) :
    f.prefixFunction (u ++ [x]) = f.prefixFunction u ++ (f.residual u).prefixFunction [x] :=
  prefixFunction_eq_of_forall fun w ↦ by
    rw [List.append_assoc, prefixFunction_append_residual]

theorem prefixFunction_append_residual_nil (f : List α → List β) (u : List α) :
    f.prefixFunction u ++ f.residual u [] = f u := by
  simpa using prefixFunction_append_residual (f := f) u []

/-- A function that appends to a function growing by blocks a final output, both read off the
summary, has residuals that factor through the summary. -/
theorem factorsThrough_residual_of_append_final {P : List α → List β} (δ : γ → α → γ)
    (g : γ → α → List β) (t : γ → List β) (hW : ∀ u x, W (u ++ [x]) = δ (W u) x)
    (hP : ∀ u x, P (u ++ [x]) = P u ++ g (W u) x) (hf : ∀ u, f u = P u ++ t (W u)) :
    f.residual.FactorsThrough W := by
  have hpre := isPrefix_append_of_append_singleton fun u x ↦ ⟨_, (hP u x).symm⟩
  have hres := factorsThrough_residual_of_append_singleton δ g hW hP
  have key (u : List α) : f.residual u =
      residual (fun w ↦ P.residual u w ++ t (w.foldl δ (W u))) [] :=
    residual_eq_of_forall (P := P u) fun w ↦ by
      rw [hf, ← append_residual (hpre u) w, List.append_assoc, List.nil_append,
        foldl_eq_of_append_singleton hW]
  intro u₁ u₂ h
  rw [key, key, hres h, h]

/-- If the residuals of `f` factor through a summary, then its prefix function grows by blocks
read off the summary, and so does what `f` adds to it at the end of the word. -/
theorem exists_prefixFunction_append_singleton_of_factorsThrough_residual
    (hW : f.residual.FactorsThrough W) :
    ∃ (g : γ → α → List β) (t : γ → List β),
      (∀ u x, f.prefixFunction (u ++ [x]) = f.prefixFunction u ++ g (W u) x) ∧
        ∀ u, f u = f.prefixFunction u ++ t (W u) := by
  refine ⟨fun c x ↦ (Function.extend W f.residual (fun _ _ ↦ []) c).prefixFunction [x],
    fun c ↦ Function.extend W f.residual (fun _ _ ↦ []) c [], fun u x ↦ ?_, fun u ↦ ?_⟩
  · dsimp only
    rw [hW.extend_apply, prefixFunction_append_singleton]
  · dsimp only
    rw [hW.extend_apply, prefixFunction_append_residual_nil]

end StateSummary

end Function

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
