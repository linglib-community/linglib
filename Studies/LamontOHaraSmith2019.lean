/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Phonology.Subregular.WeakDeterminism
public import Linglib.Phonology.Tone.Plateauing

/-!
# Lamont, O'Hara and Smith (2019): Weakly deterministic transformations are subregular

Unbounded tonal plateauing turns every toneless unit between two high tones into a high tone, so
the fate of a target depends on material unboundedly far away on both sides. Heinz and Lai, and
Jardine after them, conjectured that such maps are not weakly deterministic. Lamont, O'Hara and
Smith show that plateauing is weakly deterministic in Heinz and Lai's sense (Figure 1). A
left-to-right pass that preserves length and alphabet rewrites every HLH as HHH, so that HLH
never survives it, and then writes HLH as a code for an H with another H to its left; a
right-to-left pass decodes it.

## Main definitions

* `markLeft`, `resolveRight`: the transducers A and B of Figure 1

## Main results

* `utp_map_eq_resolve_mark`: B after A computes plateauing
* `length_markLeft_run`: A preserves length
* `utp_isWeaklyDeterministic`: plateauing is weakly deterministic

## Implementation notes

* A toneless unit is `Tone.TBU.O`, the paper's L. Since `SubsequentialTransducer.runRight`
  reverses the run, B's blocks are written reversed. The figure gives B no H transition from
  `q4`; A never writes an H there, and B keeps it.
* The proof splits a word into Ls, an H, blocks `Lʲ H`, and Ls. A writes each block as H, HH or
  `Lʲ⁻² HLH`, and B, reading right to left, holds back at most one H.
* Not formalized: §2, where first-last plateauing and double-edged spread are shown regular but
  not weakly deterministic by a counting argument, and the characterization of Theorem 3.1.

## References

* [lamont-ohara-smith-2019]
* [heinz-lai-2013]
* [jardine-2016a]
-/

@[expose] public section

namespace LamontOHaraSmith2019

open Tone List

/-! ### The transducers -/

/-- A is in `q0` before any H, in `q1` after an H with nothing held back, in `q2` holding back one
L, and in `q3` having held back two. -/
inductive MarkState
  | q0 | q1 | q2 | q3
  deriving DecidableEq, Repr, Fintype

/-- The transitions of A. -/
@[simp] def markStep : MarkState → TBU → MarkState
  | .q0, .O => .q0 | .q0, .H => .q1
  | .q1, .H => .q1 | .q1, .O => .q2
  | .q2, .H => .q1 | .q2, .O => .q3
  | .q3, .O => .q3 | .q3, .H => .q1

/-- The blocks A writes. -/
@[simp] def markOutput : MarkState → TBU → List TBU
  | .q0, a => [a]
  | .q1, .H => [.H] | .q1, .O => []
  | .q2, .H => [.H, .H] | .q2, .O => []
  | .q3, .O => [.O] | .q3, .H => [.H, .O, .H]

/-- What A writes at the end of the word, the Ls it holds back. -/
@[simp] def markFinal : MarkState → List TBU
  | .q2 => [.O]
  | .q3 => [.O, .O]
  | _ => []

/-- Transducer A of Figure 1, the left-to-right pass. -/
def markLeft : SubsequentialTransducer MarkState TBU TBU where
  start := .q0
  step := markStep
  output := markOutput
  finalOutput := markFinal

@[simp] theorem markLeft_start : markLeft.start = .q0 := rfl
@[simp] theorem markLeft_step : markLeft.step = markStep := rfl
@[simp] theorem markLeft_output : markLeft.output = markOutput := rfl
@[simp] theorem markLeft_finalOutput : markLeft.finalOutput = markFinal := rfl

/-- Reading right to left, B is in `q0` before any H, in `q1` holding back an H, in `q2` holding
back an L and an H, in `q3` inside a plateau, and in `q4` past the last code. -/
inductive ResolveState
  | q0 | q1 | q2 | q3 | q4
  deriving DecidableEq, Repr, Fintype

/-- The transitions of B. -/
@[simp] def resolveStep : ResolveState → TBU → ResolveState
  | .q0, .O => .q0 | .q0, .H => .q1
  | .q1, .H => .q1 | .q1, .O => .q2
  | .q2, .O => .q4 | .q2, .H => .q3
  | .q3, .O => .q3 | .q3, .H => .q1
  | .q4, _ => .q4

/-- The blocks B writes, each reversed. -/
@[simp] def resolveOutput : ResolveState → TBU → List TBU
  | .q0, .O => [.O] | .q0, .H => []
  | .q1, .H => [.H] | .q1, .O => []
  | .q2, .O => [.H, .O, .O] | .q2, .H => [.H, .H, .H]
  | .q3, .O => [.H] | .q3, .H => []
  | .q4, a => [a]

/-- What B writes at the end of the word, reversed. -/
@[simp] def resolveFinal : ResolveState → List TBU
  | .q1 => [.H]
  | .q2 => [.H, .O]
  | _ => []

/-- Transducer B of Figure 1, the right-to-left pass, as run by `runRight`. -/
def resolveRight : SubsequentialTransducer ResolveState TBU TBU where
  start := .q0
  step := resolveStep
  output := resolveOutput
  finalOutput := resolveFinal

@[simp] theorem resolveRight_start : resolveRight.start = .q0 := rfl
@[simp] theorem resolveRight_step : resolveRight.step = resolveStep := rfl
@[simp] theorem resolveRight_output : resolveRight.output = resolveOutput := rfl
@[simp] theorem resolveRight_finalOutput : resolveRight.finalOutput = resolveFinal := rfl

/-- In the derivation of Figure 2, A writes the code HLH for the long plateau and B decodes it. -/
example : markLeft.run [.H, .O, .H, .H, .O, .O, .O, .O, .H]
    = [.H, .H, .H, .H, .O, .O, .H, .O, .H] ∧
    resolveRight.runRight [.H, .H, .H, .H, .O, .O, .H, .O, .H] = replicate 9 .H := by
  decide

/-! ### The first pass -/

/-- What A writes for a block `Lʲ H` after an H. -/
private def code : ℕ → List TBU
  | 0 => [.H]
  | 1 => [.H, .H]
  | j + 2 => replicate j .O ++ [.H, .O, .H]

private theorem length_code (j : ℕ) : (code j).length = j + 1 := by
  rcases j with _ | _ | j <;> simp [code]

/-- The blocks `Lʲ H`, one for each entry of `js`. -/
private def blocks : List ℕ → List TBU
  | [] => []
  | j :: js => replicate j .O ++ .H :: blocks js

/-- What A writes for `blocks js`. -/
private def codes : List ℕ → List TBU
  | [] => []
  | j :: js => code j ++ codes js

private theorem length_codes (js : List ℕ) : (codes js).length = (blocks js).length := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [codes, blocks, length_code, ih]; omega

private theorem markLeft_replicate (s : MarkState) (hs : s = .q0 ∨ s = .q3) (k : ℕ) :
    markLeft.evalFrom s (replicate k .O) = s ∧
      markLeft.emitted s (replicate k .O) = replicate k .O := by
  induction k with
  | zero => simp
  | succ k ih => rcases hs with rfl | rfl <;> simp [replicate_succ, ih.1, ih.2]

private theorem markLeft_block (j : ℕ) (rest : List TBU) :
    markLeft.runFrom .q1 (replicate j .O ++ .H :: rest) = code j ++ markLeft.runFrom .q1 rest := by
  rcases j with _ | _ | j
  · simp [code]
  · simp [code]
  · rw [replicate_succ, replicate_succ, cons_append, cons_append,
      SubsequentialTransducer.runFrom_cons, SubsequentialTransducer.runFrom_cons,
      SubsequentialTransducer.runFrom_append]
    have h := markLeft_replicate .q3 (.inr rfl) j
    simp [h.1, h.2, code]

private theorem markLeft_tail (t : ℕ) :
    markLeft.runFrom .q1 (replicate t .O) = replicate t .O := by
  rcases t with _ | _ | t
  · simp
  · simp
  · rw [replicate_succ, replicate_succ, SubsequentialTransducer.runFrom_cons,
      SubsequentialTransducer.runFrom_cons, SubsequentialTransducer.runFrom]
    have h := markLeft_replicate .q3 (.inr rfl) t
    simp only [markLeft_step, markStep, markLeft_output, markOutput, h.1, h.2,
      markLeft_finalOutput, markFinal, nil_append]
    rw [show [TBU.O, TBU.O] = replicate 2 TBU.O from rfl, ← replicate_add]
    rfl

private theorem markLeft_run (a : ℕ) (js : List ℕ) (t : ℕ) :
    markLeft.run (replicate a .O ++ .H :: (blocks js ++ replicate t .O))
      = replicate a .O ++ .H :: (codes js ++ replicate t .O) := by
  have hq1 : ∀ js : List ℕ, markLeft.runFrom .q1 (blocks js ++ replicate t .O) =
      codes js ++ replicate t .O := fun js ↦ by
    induction js with
    | nil => simpa [blocks, codes] using markLeft_tail t
    | cons j js ih =>
      rw [blocks, codes, append_assoc, cons_append, markLeft_block, ih, append_assoc]
  rw [SubsequentialTransducer.run, SubsequentialTransducer.runFrom_append, markLeft_start,
    (markLeft_replicate .q0 (.inl rfl) a).1, (markLeft_replicate .q0 (.inl rfl) a).2,
    SubsequentialTransducer.runFrom_cons, markLeft_step, markStep, hq1]
  rfl

/-! ### The second pass -/

/-- B holds back one H exactly in `q1`. -/
private def held : ResolveState → ℕ
  | .q1 => 1
  | _ => 0

/-- The states B can be in between two codes. -/
private def Boundary (s : ResolveState) : Prop := s = .q0 ∨ s = .q1 ∨ s = .q3

private theorem resolveRight_replicate (k : ℕ) :
    (resolveRight.evalFrom .q0 (replicate k .O) = .q0 ∧
      resolveRight.emitted .q0 (replicate k .O) = replicate k .O) ∧
    (resolveRight.evalFrom .q3 (replicate k .O) = .q3 ∧
      resolveRight.emitted .q3 (replicate k .O) = replicate k .H) ∧
    resolveRight.runFrom .q4 (replicate k .O) = replicate k .O := by
  induction k with
  | zero => simp
  | succ k ih => simp [replicate_succ, ih.1.1, ih.1.2, ih.2.1.1, ih.2.1.2, ih.2.2]

private theorem resolveRight_code {s : ResolveState} (hs : Boundary s) (j : ℕ) :
    Boundary (resolveRight.evalFrom s (code j).reverse) ∧
      ∃ n, resolveRight.emitted s (code j).reverse = replicate n .H ∧
        n + held (resolveRight.evalFrom s (code j).reverse) = j + 1 + held s := by
  rcases j with _ | _ | j
  · rcases hs with rfl | rfl | rfl <;> simp [code, Boundary, held]
  · rcases hs with rfl | rfl | rfl <;> simp [code, Boundary, held]
  · have hr : (code (j + 2)).reverse = [.H, .O, .H] ++ replicate j .O := by simp [code]
    rw [hr, Mealy.evalFrom_append, SubsequentialTransducer.emitted_append]
    have h := (resolveRight_replicate j).2.1
    rcases hs with rfl | rfl | rfl <;> simp [Boundary, held, h.1, h.2, ← replicate_succ]

private theorem resolveRight_codes {s : ResolveState} (hs : Boundary s) (js : List ℕ) :
    Boundary (resolveRight.evalFrom s (codes js).reverse) ∧
      ∃ n, resolveRight.emitted s (codes js).reverse = replicate n .H ∧
        n + held (resolveRight.evalFrom s (codes js).reverse) = (codes js).length + held s := by
  induction js generalizing s with
  | nil => exact ⟨hs, 0, rfl, by simp [codes]⟩
  | cons j js ih =>
    obtain ⟨hg, n, hn, hc⟩ := ih hs
    obtain ⟨hg', m, hm, hc'⟩ := resolveRight_code hg j
    simp only [codes, reverse_append, Mealy.evalFrom_append,
      SubsequentialTransducer.emitted_append, hn, hm, length_append, length_code]
    exact ⟨hg', n + m, by rw [replicate_add], by omega⟩

private theorem resolveRight_head {s : ResolveState} (hs : Boundary s) :
    resolveRight.evalFrom s [.H] = .q1 ∧ resolveRight.emitted s [.H] = replicate (held s) .H := by
  rcases hs with rfl | rfl | rfl <;> simp [held]

private theorem resolveRight_prefix (a : ℕ) :
    (resolveRight.runFrom .q1 (replicate a .O)).reverse = replicate a .O ++ [.H] := by
  rcases a with _ | _ | a
  · simp
  · simp
  · rw [replicate_succ, replicate_succ, SubsequentialTransducer.runFrom_cons,
      SubsequentialTransducer.runFrom_cons]
    simp only [(resolveRight_replicate a).2.2, resolveRight_output, resolveOutput,
      resolveRight_step, resolveStep, nil_append, reverse_append, reverse_replicate, reverse_cons,
      reverse_nil]
    rw [show ([TBU.O] ++ [TBU.O] ++ [TBU.H]) = replicate 2 TBU.O ++ [TBU.H] from rfl,
      ← append_assoc, ← replicate_add]
    rfl

private theorem resolve_mark (a : ℕ) (js : List ℕ) (t : ℕ) :
    resolveRight.runRight (markLeft.run (replicate a .O ++ .H :: (blocks js ++ replicate t .O)))
      = replicate a .O ++ .H :: (replicate (blocks js).length .H ++ replicate t .O) := by
  rw [markLeft_run, SubsequentialTransducer.runRight, SubsequentialTransducer.run]
  have hrev : (replicate a TBU.O ++ TBU.H :: (codes js ++ replicate t .O)).reverse
      = replicate t .O ++ ((codes js).reverse ++ [.H]) ++ replicate a .O := by simp
  obtain ⟨hg, n, hn, hc⟩ := resolveRight_codes (s := .q0) (.inl rfl) js
  obtain ⟨h1, h2⟩ := resolveRight_head hg
  rw [hrev, SubsequentialTransducer.runFrom_append, SubsequentialTransducer.emitted_append,
    Mealy.evalFrom_append, resolveRight_start, (resolveRight_replicate t).1.1,
    (resolveRight_replicate t).1.2, SubsequentialTransducer.emitted_append, hn,
    Mealy.evalFrom_append, h1, h2]
  simp only [reverse_append, resolveRight_prefix, reverse_replicate, append_assoc,
    ← replicate_add]
  rw [← length_codes]
  rw [show held .q0 = 0 from rfl, add_zero] at hc
  rw [hc]
  simp

/-! ### Plateauing -/

private theorem exists_blocks (u : List TBU) : ∃ js t, u = blocks js ++ replicate t .O := by
  induction u with
  | nil => exact ⟨[], 0, rfl⟩
  | cons x u ih =>
    obtain ⟨js, t, rfl⟩ := ih
    cases x with
    | H => exact ⟨0 :: js, t, rfl⟩
    | O =>
      cases js with
      | nil => exact ⟨[], t + 1, rfl⟩
      | cons j js => exact ⟨(j + 1) :: js, t, rfl⟩

private theorem decomposition (w : List TBU) :
    (∃ a, w = replicate a .O) ∨
      ∃ a js t, w = replicate a .O ++ .H :: (blocks js ++ replicate t .O) := by
  induction w with
  | nil => exact .inl ⟨0, rfl⟩
  | cons x w ih =>
    cases x with
    | H =>
      obtain ⟨js, t, rfl⟩ := exists_blocks w
      exact .inr ⟨0, js, t, rfl⟩
    | O =>
      rcases ih with ⟨a, rfl⟩ | ⟨a, js, t, rfl⟩
      · exact .inl ⟨a + 1, rfl⟩
      · exact .inr ⟨a + 1, js, t, rfl⟩

private theorem blocks_eq_append {js : List ℕ} (h : js ≠ []) : ∃ m, blocks js = m ++ [.H] := by
  induction js with
  | nil => exact absurd rfl h
  | cons j js ih =>
    rcases js with _ | ⟨k, ks⟩
    · exact ⟨replicate j .O, rfl⟩
    · obtain ⟨m, hm⟩ := ih (cons_ne_nil _ _)
      exact ⟨replicate j .O ++ .H :: m, by rw [blocks, hm]; simp⟩

private theorem utp_map_blocks (a : ℕ) (js : List ℕ) (t : ℕ) :
    utp.map (replicate a .O ++ .H :: (blocks js ++ replicate t .O))
      = replicate a .O ++ .H :: (replicate (blocks js).length .H ++ replicate t .O) := by
  rcases eq_or_ne js [] with rfl | h
  · simpa [blocks] using utp.map_single a t
  · obtain ⟨m, hm⟩ := blocks_eq_append h
    rw [hm, append_assoc, singleton_append, utp.map_plateau]
    simp [replicate_succ]

/-- B after A computes unbounded tonal plateauing (Figure 1). -/
theorem utp_map_eq_resolve_mark (w : List TBU) :
    utp.map w = resolveRight.runRight (markLeft.run w) := by
  rcases decomposition w with ⟨a, rfl⟩ | ⟨a, js, t, rfl⟩
  · simp only [utp.map_toneless, SubsequentialTransducer.runRight, SubsequentialTransducer.run,
      SubsequentialTransducer.runFrom, markLeft_start, (markLeft_replicate .q0 (.inl rfl) a).1,
      (markLeft_replicate .q0 (.inl rfl) a).2, markLeft_finalOutput, markFinal, append_nil,
      reverse_replicate, resolveRight_start, (resolveRight_replicate a).1.1,
      (resolveRight_replicate a).1.2, resolveRight_finalOutput, resolveFinal]
  · rw [resolve_mark, utp_map_blocks]

theorem length_markLeft_run (w : List TBU) : (markLeft.run w).length = w.length := by
  rcases decomposition w with ⟨a, rfl⟩ | ⟨a, js, t, rfl⟩
  · simp [SubsequentialTransducer.run, SubsequentialTransducer.runFrom,
      (markLeft_replicate .q0 (.inl rfl) a).1, (markLeft_replicate .q0 (.inl rfl) a).2]
  · rw [markLeft_run]; simp [length_codes]

theorem utp_isWeaklyDeterministic : IsWeaklyDeterministic utp.map :=
  ⟨markLeft.run, resolveRight.runRight, markLeft.isLeftSubsequential,
    fun w ↦ (length_markLeft_run w).le, resolveRight.isRightSubsequential,
    funext fun w ↦ (utp_map_eq_resolve_mark w).symm⟩

end LamontOHaraSmith2019
