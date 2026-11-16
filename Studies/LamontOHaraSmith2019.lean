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
Smith show that [plateauing is weakly deterministic](##utp_isWeaklyDeterministic) in Heinz and
Lai's sense: a left-to-right pass that preserves length and alphabet rewrites every HLH as HHH and
then writes HLH as a code for an H with another H to its left, and a right-to-left pass decodes
it. They go on to two variants, first-last plateauing, where a word plateaus only when its first
and last units are high, and double-edged spread, where the first high tone spreads to the left
edge of the word and the last to the right edge. Under the same definition
[both](##firstLast_isWeaklyDeterministic) [variants](##doubleEdged_isWeaklyDeterministic) are
weakly deterministic, by a first pass that moves the first unit of the word to its end.

## Implementation notes

* A toneless unit is `Tone.AssociationState.O`, the paper's L. Since
  `SubsequentialTransducer.runRight` reverses the run, the blocks of a right-to-left pass are
  written reversed. The figure gives B no H transition from `q4`; A never writes an H there, and B
  keeps it.
* The proof for plateauing splits a word into Ls, an H, blocks `Lʲ H`, and Ls. A writes each block
  as H, HH or `Lʲ⁻² HLH`, and B, reading right to left, holds back at most one H.
* The paper presents first-last plateauing and double-edged spread as regular maps outside the
  weakly deterministic class, on the ground that a first pass must leave its markup within a
  bounded window of the edge it describes. `IsWeaklyDeterministic` asks of the first pass only
  that it be left-subsequential and not lengthen its input, over the same alphabet, and a pass
  that writes the first unit last meets that: `rotate` and `spreadEdge` both preserve length. For
  double-edged spread the first unit need not be kept, since it surfaces H exactly when the word
  has an H, and the first pass ends the word with that fact instead.
* The two variants are defined directly as maps, not by the non-deterministic transducers of the
  paper's figures.

## TODO

* Whether the weakly deterministic maps are a proper subclass of the regular ones is not settled
  here: the file has no regular map proved outside `IsWeaklyDeterministic`.
* The characterization of the weakly deterministic unbounded circumambient maps by banned
  substrings (the paper's last section) is not formalized.

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
@[simp] def markStep : MarkState → AssociationState → MarkState
  | .q0, .O => .q0 | .q0, .H => .q1
  | .q1, .H => .q1 | .q1, .O => .q2
  | .q2, .H => .q1 | .q2, .O => .q3
  | .q3, .O => .q3 | .q3, .H => .q1

/-- The blocks A writes. -/
@[simp] def markOutput : MarkState → AssociationState → List AssociationState
  | .q0, a => [a]
  | .q1, .H => [.H] | .q1, .O => []
  | .q2, .H => [.H, .H] | .q2, .O => []
  | .q3, .O => [.O] | .q3, .H => [.H, .O, .H]

/-- What A writes at the end of the word, the Ls it holds back. -/
@[simp] def markFinal : MarkState → List AssociationState
  | .q2 => [.O]
  | .q3 => [.O, .O]
  | _ => []

/-- Transducer A of Figure 1, the left-to-right pass. -/
def markLeft : SubsequentialTransducer MarkState AssociationState AssociationState where
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
@[simp] def resolveStep : ResolveState → AssociationState → ResolveState
  | .q0, .O => .q0 | .q0, .H => .q1
  | .q1, .H => .q1 | .q1, .O => .q2
  | .q2, .O => .q4 | .q2, .H => .q3
  | .q3, .O => .q3 | .q3, .H => .q1
  | .q4, _ => .q4

/-- The blocks B writes, each reversed. -/
@[simp] def resolveOutput : ResolveState → AssociationState → List AssociationState
  | .q0, .O => [.O] | .q0, .H => []
  | .q1, .H => [.H] | .q1, .O => []
  | .q2, .O => [.H, .O, .O] | .q2, .H => [.H, .H, .H]
  | .q3, .O => [.H] | .q3, .H => []
  | .q4, a => [a]

/-- What B writes at the end of the word, reversed. -/
@[simp] def resolveFinal : ResolveState → List AssociationState
  | .q1 => [.H]
  | .q2 => [.H, .O]
  | _ => []

/-- Transducer B of Figure 1, the right-to-left pass, as run by `runRight`. -/
def resolveRight : SubsequentialTransducer ResolveState AssociationState AssociationState where
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
private def code : ℕ → List AssociationState
  | 0 => [.H]
  | 1 => [.H, .H]
  | j + 2 => replicate j .O ++ [.H, .O, .H]

private theorem length_code (j : ℕ) : (code j).length = j + 1 := by
  rcases j with _ | _ | j <;> simp [code]

/-- The blocks `Lʲ H`, one for each entry of `js`. -/
private def blocks : List ℕ → List AssociationState
  | [] => []
  | j :: js => replicate j .O ++ .H :: blocks js

/-- What A writes for `blocks js`. -/
private def codes : List ℕ → List AssociationState
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

private theorem markLeft_block (j : ℕ) (rest : List AssociationState) :
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
    rw [show [AssociationState.O, AssociationState.O] = replicate 2 AssociationState.O from rfl,
      ← replicate_add]
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
    rw [show ([AssociationState.O] ++ [AssociationState.O] ++ [AssociationState.H]) =
        replicate 2 AssociationState.O ++ [AssociationState.H] from rfl,
      ← append_assoc, ← replicate_add]
    rfl

private theorem resolve_mark (a : ℕ) (js : List ℕ) (t : ℕ) :
    resolveRight.runRight (markLeft.run (replicate a .O ++ .H :: (blocks js ++ replicate t .O)))
      = replicate a .O ++ .H :: (replicate (blocks js).length .H ++ replicate t .O) := by
  rw [markLeft_run, SubsequentialTransducer.runRight, SubsequentialTransducer.run]
  have hrev :
      (replicate a AssociationState.O ++ AssociationState.H :: (codes js ++ replicate t .O)).reverse
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

private theorem exists_blocks (u : List AssociationState) :
    ∃ js t, u = blocks js ++ replicate t .O := by
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

private theorem decomposition (w : List AssociationState) :
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
theorem utp_map_eq_resolve_mark (w : List AssociationState) :
    utp.map w = resolveRight.runRight (markLeft.run w) := by
  rcases decomposition w with ⟨a, rfl⟩ | ⟨a, js, t, rfl⟩
  · simp only [utp.map_toneless, SubsequentialTransducer.runRight, SubsequentialTransducer.run,
      SubsequentialTransducer.runFrom, markLeft_start, (markLeft_replicate .q0 (.inl rfl) a).1,
      (markLeft_replicate .q0 (.inl rfl) a).2, markLeft_finalOutput, markFinal, append_nil,
      reverse_replicate, resolveRight_start, (resolveRight_replicate a).1.1,
      (resolveRight_replicate a).1.2, resolveRight_finalOutput, resolveFinal]
  · rw [resolve_mark, utp_map_blocks]

theorem length_markLeft_run (w : List AssociationState) : (markLeft.run w).length = w.length := by
  rcases decomposition w with ⟨a, rfl⟩ | ⟨a, js, t, rfl⟩
  · simp [SubsequentialTransducer.run, SubsequentialTransducer.runFrom,
      (markLeft_replicate .q0 (.inl rfl) a).1, (markLeft_replicate .q0 (.inl rfl) a).2]
  · rw [markLeft_run]; simp [length_codes]

/-- Unbounded tonal plateauing is weakly deterministic in Heinz and Lai's sense. -/
theorem utp_isWeaklyDeterministic : IsWeaklyDeterministic utp.map :=
  ⟨markLeft.run, resolveRight.runRight, markLeft.isLeftSubsequential,
    fun w ↦ (length_markLeft_run w).le, resolveRight.isRightSubsequential,
    funext fun w ↦ (utp_map_eq_resolve_mark w).symm⟩

/-! ### First-last plateauing -/

/-- First-last plateauing makes every unit high when the first and the last unit are high, and
changes nothing otherwise. -/
def firstLast (w : List AssociationState) : List AssociationState :=
  if w.head? = some .H ∧ w.getLast? = some .H then replicate w.length .H else w

example : firstLast [.H, .O, .O, .O, .H] = replicate 5 .H ∧
    firstLast [.H, .O, .O, .H, .O] = [.H, .O, .O, .H, .O] := by
  decide

/-- The first pass is in `q0` before the first unit, and afterwards in `qH` or `qL` according to
what that unit was. -/
inductive RotateState
  | q0 | qH | qL
  deriving DecidableEq, Repr, Fintype

/-- The transitions of the first pass. -/
@[simp] def rotateStep : RotateState → AssociationState → RotateState
  | .q0, .H => .qH | .q0, .O => .qL
  | .qH, _ => .qH
  | .qL, _ => .qL

/-- The first pass writes nothing for the first unit and copies the rest. -/
@[simp] def rotateOutput : RotateState → AssociationState → List AssociationState
  | .q0, _ => []
  | .qH, a => [a]
  | .qL, a => [a]

/-- At the end of the word the first pass writes the first unit. -/
@[simp] def rotateFinal : RotateState → List AssociationState
  | .q0 => []
  | .qH => [.H]
  | .qL => [.O]

/-- The left-to-right pass that moves the first unit of a word to its end. -/
def rotate : SubsequentialTransducer RotateState AssociationState AssociationState where
  start := .q0
  step := rotateStep
  output := rotateOutput
  finalOutput := rotateFinal

@[simp] theorem rotate_start : rotate.start = .q0 := rfl
@[simp] theorem rotate_step : rotate.step = rotateStep := rfl
@[simp] theorem rotate_output : rotate.output = rotateOutput := rfl
@[simp] theorem rotate_finalOutput : rotate.finalOutput = rotateFinal := rfl

private theorem rotate_runFrom {s : RotateState} (hs : s ≠ .q0) (w : List AssociationState) :
    rotate.runFrom s w = w ++ rotateFinal s := by
  induction w with
  | nil => simp
  | cons a w ih => cases s <;> simp_all

theorem rotate_run_cons (a : AssociationState) (w : List AssociationState) :
    rotate.run (a :: w) = w ++ [a] := by
  cases a <;> simp [SubsequentialTransducer.run, rotate_runFrom]

theorem length_rotate_run (w : List AssociationState) : (rotate.run w).length = w.length := by
  rcases w with _ | ⟨a, w⟩
  · rfl
  · simp [rotate_run_cons]

/-- Reading right to left, the second pass is in `q0` before the moved unit, in `q1` copying after
a moved L, in `q2` after a moved H, in `q3` copying after a moved H and a final L, and in `q4`
writing Hs after a moved H and a final H. -/
inductive PlateauState
  | q0 | q1 | q2 | q3 | q4
  deriving DecidableEq, Repr, Fintype

/-- The transitions of the second pass. -/
@[simp] def plateauStep : PlateauState → AssociationState → PlateauState
  | .q0, .H => .q2 | .q0, .O => .q1
  | .q1, _ => .q1
  | .q2, .H => .q4 | .q2, .O => .q3
  | .q3, _ => .q3
  | .q4, _ => .q4

/-- The second pass copies, except that it writes nothing for the moved unit and writes H for
every unit once the moved unit and the final unit are both H. -/
@[simp] def plateauOutput : PlateauState → AssociationState → List AssociationState
  | .q0, _ => []
  | .q1, a => [a]
  | .q2, a => [a]
  | .q3, a => [a]
  | .q4, _ => [.H]

/-- At the end of the word the second pass writes the moved unit back. -/
@[simp] def plateauFinal : PlateauState → List AssociationState
  | .q0 => []
  | .q1 => [.O]
  | _ => [.H]

/-- The right-to-left pass that reads the moved first unit, then the last unit, and plateaus when
both are H, as run by `runRight`. -/
def plateauRight : SubsequentialTransducer PlateauState AssociationState AssociationState where
  start := .q0
  step := plateauStep
  output := plateauOutput
  finalOutput := plateauFinal

@[simp] theorem plateauRight_start : plateauRight.start = .q0 := rfl
@[simp] theorem plateauRight_step : plateauRight.step = plateauStep := rfl
@[simp] theorem plateauRight_output : plateauRight.output = plateauOutput := rfl
@[simp] theorem plateauRight_finalOutput : plateauRight.finalOutput = plateauFinal := rfl

private theorem plateauRight_runFrom (w : List AssociationState) :
    plateauRight.runFrom .q1 w = w ++ [.O] ∧ plateauRight.runFrom .q3 w = w ++ [.H] ∧
      plateauRight.runFrom .q4 w = replicate (w.length + 1) .H := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih, replicate_succ]

theorem firstLast_eq_plateau_rotate (w : List AssociationState) :
    firstLast w = plateauRight.runRight (rotate.run w) := by
  rcases w with _ | ⟨a, w⟩
  · decide
  · rw [rotate_run_cons]
    rcases eq_nil_or_concat w with rfl | ⟨u, c, rfl⟩
    · cases a <;> decide
    · have hl : (a :: (u ++ [c])).getLast? = some c := by rw [← cons_append, getLast?_concat]
      cases a <;> cases c <;>
        simp [firstLast, hl, SubsequentialTransducer.runRight, SubsequentialTransducer.run,
          plateauRight_runFrom, ← replicate_succ]

/-- First-last plateauing is weakly deterministic in Heinz and Lai's sense: a left-to-right pass
moves the first unit to the end of the word, where the right-to-left pass reads it first. -/
theorem firstLast_isWeaklyDeterministic : IsWeaklyDeterministic firstLast :=
  ⟨rotate.run, plateauRight.runRight, rotate.isLeftSubsequential,
    fun w ↦ (length_rotate_run w).le, plateauRight.isRightSubsequential,
    funext fun w ↦ (firstLast_eq_plateau_rotate w).symm⟩

/-! ### Double-edged spread -/

/-- The first H of a word spreads to its left edge. -/
def spreadLeft : List AssociationState → List AssociationState
  | [] => []
  | .H :: w => .H :: w
  | .O :: w => .H :: spreadLeft w

/-- In double-edged spread the first H of a word spreads to its left edge and the last H to its
right edge; a word without an H is unchanged. -/
def doubleEdged (w : List AssociationState) : List AssociationState :=
  if .H ∈ w then spreadLeft (spreadLeft w.reverse).reverse else w

example : doubleEdged [.O, .O, .O, .H, .O, .O, .H, .O, .O, .H, .O, .O, .O]
    = [.H, .H, .H, .H, .O, .O, .H, .O, .O, .H, .H, .H, .H] ∧
    doubleEdged [.O, .O, .O, .O] = [.O, .O, .O, .O] := by
  decide

private theorem spreadLeft_append_H (v r : List AssociationState) :
    spreadLeft (v ++ .H :: r) = spreadLeft v ++ .H :: r := by
  induction v with
  | nil => rfl
  | cons a v ih => cases a <;> simp [spreadLeft, ih]

private theorem spreadLeft_replicate (n : ℕ) :
    spreadLeft (replicate n .O) = replicate n .H := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicate_succ, spreadLeft, ih]

/-- The first pass is in `q0` before the first unit, in `q1` having read only Ls, and in `q2`
after an H. -/
inductive EdgeState
  | q0 | q1 | q2
  deriving DecidableEq, Repr, Fintype

/-- The transitions of the first pass. -/
@[simp] def edgeStep : EdgeState → AssociationState → EdgeState
  | .q0, .H => .q2 | .q0, .O => .q1
  | .q1, .H => .q2 | .q1, .O => .q1
  | .q2, _ => .q2

/-- The first pass writes nothing for the first unit, H for every other unit up to the first H,
and copies the rest. -/
@[simp] def edgeOutput : EdgeState → AssociationState → List AssociationState
  | .q0, _ => []
  | .q1, _ => [.H]
  | .q2, a => [a]

/-- At the end of the word the first pass writes whether the word had an H. -/
@[simp] def edgeFinal : EdgeState → List AssociationState
  | .q0 => []
  | .q1 => [.O]
  | .q2 => [.H]

/-- The left-to-right pass that spreads the first H leftward, drops the first unit, and ends the
word with an H exactly when it had one. -/
def spreadEdge : SubsequentialTransducer EdgeState AssociationState AssociationState where
  start := .q0
  step := edgeStep
  output := edgeOutput
  finalOutput := edgeFinal

@[simp] theorem spreadEdge_start : spreadEdge.start = .q0 := rfl
@[simp] theorem spreadEdge_step : spreadEdge.step = edgeStep := rfl
@[simp] theorem spreadEdge_output : spreadEdge.output = edgeOutput := rfl
@[simp] theorem spreadEdge_finalOutput : spreadEdge.finalOutput = edgeFinal := rfl

private theorem spreadEdge_runFrom_q2 (w : List AssociationState) :
    spreadEdge.runFrom .q2 w = w ++ [.H] := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

private theorem spreadEdge_runFrom_q1 (k : ℕ) :
    spreadEdge.runFrom .q1 (replicate k .O) = replicate k .H ++ [.O] ∧
      ∀ u, spreadEdge.runFrom .q1 (replicate k .O ++ .H :: u)
        = replicate k .H ++ .H :: (u ++ [.H]) := by
  induction k with
  | zero => simp [spreadEdge_runFrom_q2]
  | succ k ih => simp [replicate_succ, ih.1, ih.2]

/-- Reading right to left, the second pass is in `q0` before the last unit, in `q1` when that unit
says the word has no H, in `q2` up to the last H of the word, and in `q3` after it. -/
inductive CloseState
  | q0 | q1 | q2 | q3
  deriving DecidableEq, Repr, Fintype

/-- The transitions of the second pass. -/
@[simp] def closeStep : CloseState → AssociationState → CloseState
  | .q0, .H => .q2 | .q0, .O => .q1
  | .q1, _ => .q1
  | .q2, .H => .q3 | .q2, .O => .q2
  | .q3, _ => .q3

/-- The second pass writes nothing for the last unit, L throughout a word without an H, and
otherwise H up to the last H of the word and a copy after it. -/
@[simp] def closeOutput : CloseState → AssociationState → List AssociationState
  | .q0, _ => []
  | .q1, _ => [.O]
  | .q2, _ => [.H]
  | .q3, a => [a]

/-- At the end of the word the second pass writes the dropped first unit back. -/
@[simp] def closeFinal : CloseState → List AssociationState
  | .q0 => []
  | .q1 => [.O]
  | _ => [.H]

/-- The right-to-left pass that spreads the last H rightward and restores the first unit, as run
by `runRight`. -/
def closeRight : SubsequentialTransducer CloseState AssociationState AssociationState where
  start := .q0
  step := closeStep
  output := closeOutput
  finalOutput := closeFinal

@[simp] theorem closeRight_start : closeRight.start = .q0 := rfl
@[simp] theorem closeRight_step : closeRight.step = closeStep := rfl
@[simp] theorem closeRight_output : closeRight.output = closeOutput := rfl
@[simp] theorem closeRight_finalOutput : closeRight.finalOutput = closeFinal := rfl

private theorem closeRight_runFrom (w : List AssociationState) :
    closeRight.runFrom .q1 w = replicate (w.length + 1) .O ∧
      closeRight.runFrom .q3 w = w ++ [.H] ∧
      closeRight.runFrom .q2 w = spreadLeft w ++ [.H] := by
  induction w with
  | nil => simp [spreadLeft]
  | cons a w ih => cases a <;> simp [ih, replicate_succ, spreadLeft]

private theorem spreadEdge_run (k : ℕ) :
    spreadEdge.run (replicate (k + 1) .O) = replicate k .H ++ [.O] ∧
      ∀ u, spreadEdge.run (replicate (k + 1) .O ++ .H :: u)
        = replicate k .H ++ .H :: (u ++ [.H]) := by
  simp [SubsequentialTransducer.run, replicate_succ, spreadEdge_runFrom_q1]

theorem doubleEdged_eq_close_spread (w : List AssociationState) :
    doubleEdged w = closeRight.runRight (spreadEdge.run w) := by
  rcases decomposition w with ⟨a, rfl⟩ | ⟨a, js, t, rfl⟩
  · rcases a with _ | k
    · decide
    · rw [(spreadEdge_run k).1]
      simp [doubleEdged, SubsequentialTransducer.runRight, SubsequentialTransducer.run,
        closeRight_runFrom]
  · generalize blocks js ++ replicate t .O = u
    rcases a with _ | k
    · simp [doubleEdged, SubsequentialTransducer.runRight, SubsequentialTransducer.run,
        spreadEdge_runFrom_q2, closeRight_runFrom, spreadLeft_append_H, spreadLeft]
    · rw [(spreadEdge_run k).2]
      simp [doubleEdged, SubsequentialTransducer.runRight, SubsequentialTransducer.run,
        closeRight_runFrom, spreadLeft_append_H, spreadLeft_replicate]
      rfl

theorem length_spreadEdge_run (w : List AssociationState) :
    (spreadEdge.run w).length = w.length := by
  rcases decomposition w with ⟨a, rfl⟩ | ⟨a, js, t, rfl⟩
  · rcases a with _ | k
    · rfl
    · simp [(spreadEdge_run k).1]
  · generalize blocks js ++ replicate t .O = u
    rcases a with _ | k
    · simp [SubsequentialTransducer.run, spreadEdge_runFrom_q2]
    · simp [(spreadEdge_run k).2]; omega

/-- Double-edged spread is weakly deterministic in Heinz and Lai's sense: a left-to-right pass
spreads the first H and ends the word with a record of whether it had one, and the right-to-left
pass spreads the last H. -/
theorem doubleEdged_isWeaklyDeterministic : IsWeaklyDeterministic doubleEdged :=
  ⟨spreadEdge.run, closeRight.runRight, spreadEdge.isLeftSubsequential,
    fun w ↦ (length_spreadEdge_run w).le, closeRight.isRightSubsequential,
    funext fun w ↦ (doubleEdged_eq_close_spread w).symm⟩

end LamontOHaraSmith2019
