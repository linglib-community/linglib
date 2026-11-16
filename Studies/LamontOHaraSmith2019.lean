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

Unbounded tonal plateauing makes every toneless unit between two high tones high, so a target
depends on material unboundedly far away on both sides, and Heinz and Lai conjectured that such
maps are not weakly deterministic. Lamont, O'Hara and Smith show that [plateauing
is](##utp_isWeaklyDeterministic): a left-to-right pass that preserves length and alphabet leaves
HLH as a code for an H with another H to its left, and a right-to-left pass decodes it. Their two
variants, [first-last plateauing](##firstLast_isUnboundedCircumambient) and [double-edged
spread](##doubleEdged_isUnboundedCircumambient), depend on both sides in the same way, and under
the same definition [the first](##firstLast_isWeaklyDeterministic) and [the
second](##doubleEdged_isWeaklyDeterministic) are weakly deterministic too.

## Implementation notes

* A toneless unit is `Tone.AssociationState.O`, the paper's L. Since
  `SubsequentialTransducer.runRight` reverses the run, the blocks of a right-to-left pass are
  written reversed. The figure gives B no H transition from `q4`; A never writes an H there, and B
  keeps it.
* The proof for plateauing splits a word into Ls, an H, blocks `Lʲ H`, and Ls. A writes each block
  as H, HH or `Lʲ⁻² HLH`, and B, reading right to left, holds back at most one H.
* The two variants are stated by which units surface H, where the paper gives non-deterministic
  transducers.
* The paper presents the two variants as regular maps outside the weakly deterministic class, on
  the ground that a first pass must leave its markup within a bounded window of the edge it
  describes. `IsWeaklyDeterministic` asks of the first pass only that it be left-subsequential
  and not lengthen its input, over the same alphabet, which a pass that writes the first unit
  last meets (`IsRightSubsequential.isWeaklyDeterministic_comp_rotate`).
* For double-edged spread the first unit need not be kept, since it surfaces H exactly when the
  word has an H; the first pass ends the word with that fact instead.

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

open Tone List Subregular

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
    utp (replicate a .O ++ .H :: (blocks js ++ replicate t .O))
      = replicate a .O ++ .H :: (replicate (blocks js).length .H ++ replicate t .O) := by
  rcases eq_or_ne js [] with rfl | h
  · simpa [blocks] using utp_single a t
  · obtain ⟨m, hm⟩ := blocks_eq_append h
    rw [hm, append_assoc, singleton_append, utp_plateau]
    simp [replicate_succ]

-- B after A computes unbounded tonal plateauing (Figure 1).
theorem utp_map_eq_resolve_mark (w : List AssociationState) :
    utp w = resolveRight.runRight (markLeft.run w) := by
  rcases decomposition w with ⟨a, rfl⟩ | ⟨a, js, t, rfl⟩
  · simp only [utp_replicate_O, SubsequentialTransducer.runRight, SubsequentialTransducer.run,
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
theorem utp_isWeaklyDeterministic : IsWeaklyDeterministic utp :=
  ⟨markLeft.run, resolveRight.runRight, markLeft.isLeftSubsequential,
    fun w ↦ (length_markLeft_run w).le, resolveRight.isRightSubsequential,
    funext fun w ↦ (utp_map_eq_resolve_mark w).symm⟩

/-! ### First-last plateauing -/

/-- In first-last plateauing a unit surfaces H when it is H, or when the first and the last unit
of the word are both H. -/
def firstLast.Surfaces (w : List AssociationState) (i : ℕ) : Prop :=
  w[i]? = some .H ∨ w.head? = some .H ∧ w.getLast? = some .H

instance (w : List AssociationState) (i : ℕ) : Decidable (firstLast.Surfaces w i) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- First-last plateauing writes H at the units that surface H and L at the others. -/
def firstLast (w : List AssociationState) : List AssociationState :=
  w.mapIdx fun i _ ↦ if firstLast.Surfaces w i then .H else .O

example : firstLast [.H, .O, .O, .O, .H] = replicate 5 .H ∧
    firstLast [.H, .O, .O, .H, .O] = [.H, .O, .O, .H, .O] := by
  decide

theorem getElem?_firstLast (w : List AssociationState) (i : ℕ) :
    (firstLast w)[i]? = w[i]?.map fun _ ↦
      if firstLast.Surfaces w i then AssociationState.H else AssociationState.O := by
  simp [firstLast, getElem?_mapIdx]

theorem firstLast_eq (w : List AssociationState) :
    firstLast w
      = if w.head? = some .H ∧ w.getLast? = some .H then replicate w.length .H else w := by
  refine ext_getElem? fun i ↦ ?_
  split_ifs with h <;> rw [getElem?_firstLast]
  · rcases lt_or_ge i w.length with hi | hi
    · simp [firstLast.Surfaces, hi, h]
    · simp [hi.not_gt]
  · rcases h' : w[i]? with _ | a
    · simp
    · cases a <;> simp [firstLast.Surfaces, h, h']

/-- First-last plateauing is unbounded circumambient: a unit between two edge Hs surfaces H, and
making either edge toneless, however far away it is, leaves the unit toneless. -/
theorem firstLast_isUnboundedCircumambient : IsUnboundedCircumambient firstLast :=
  .of_flanks (fill := .O) (xOn := .H) (yOn := .H) (xOff := .O) (yOff := .O)
    (n := fun d ↦ 2 * d + 2) (t := fun d ↦ d + 1) (fun d ↦ by omega) (fun d ↦ by omega)
    (fun d ↦ by
      rw [firstLast_eq, ite_eq_left ⟨head?_flankWord, getLast?_flankWord⟩, getElem?_replicate,
        ite_eq_left (by rw [length_flankWord]; omega)]
      decide)
    (fun d ↦ by
      rw [firstLast_eq, ite_eq_right (by simp)]
      exact getElem?_flankWord_mid (by omega) (by omega))
    (fun d ↦ by
      rw [firstLast_eq, ite_eq_right (by simp)]
      exact getElem?_flankWord_mid (by omega) (by omega))

/-- Reading right to left after the first unit has been moved to the end, the second pass starts
before the moved unit, is `low` after a moved L, `high` after a moved H, `faithful` after a moved
H and a final L, and `plateau` after a moved H and a final H. -/
inductive PlateauState
  | start | low | high | faithful | plateau
  deriving DecidableEq, Repr, Fintype

/-- The transitions of the second pass. -/
@[simp] def plateauStep : PlateauState → AssociationState → PlateauState
  | .start, .H => .high | .start, .O => .low
  | .low, _ => .low
  | .high, .H => .plateau | .high, .O => .faithful
  | .faithful, _ => .faithful
  | .plateau, _ => .plateau

/-- The second pass copies, except that it writes nothing for the moved unit and writes H for
every unit once the moved unit and the final unit are both H. -/
@[simp] def plateauOutput : PlateauState → AssociationState → List AssociationState
  | .start, _ => []
  | .low, a => [a]
  | .high, a => [a]
  | .faithful, a => [a]
  | .plateau, _ => [.H]

/-- At the end of the word the second pass writes the moved unit back. -/
@[simp] def plateauFinal : PlateauState → List AssociationState
  | .start => []
  | .low => [.O]
  | _ => [.H]

/-- The right-to-left pass that reads the moved first unit, then the last unit, and plateaus when
both are H, as run by `runRight`. -/
@[simps]
def plateauRight : SubsequentialTransducer PlateauState AssociationState AssociationState where
  start := .start
  step := plateauStep
  output := plateauOutput
  finalOutput := plateauFinal

private theorem plateauRight_runFrom_low (w : List AssociationState) :
    plateauRight.runFrom .low w = w ++ [.O] := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

private theorem plateauRight_runFrom_faithful (w : List AssociationState) :
    plateauRight.runFrom .faithful w = w ++ [.H] := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

private theorem plateauRight_runFrom_plateau (w : List AssociationState) :
    plateauRight.runFrom .plateau w = replicate (w.length + 1) .H := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih, replicate_succ]

theorem firstLast_eq_plateau_rotate (w : List AssociationState) :
    firstLast w = plateauRight.runRight (w.rotate 1) := by
  rw [firstLast_eq]
  rcases w with _ | ⟨a, w⟩
  · decide
  · rw [rotate_cons_succ, rotate_zero]
    rcases eq_nil_or_concat w with rfl | ⟨u, c, rfl⟩
    · cases a <;> decide
    · have hl : (a :: (u ++ [c])).getLast? = some c := by rw [← cons_append, getLast?_concat]
      cases a <;> cases c <;>
        simp [hl, SubsequentialTransducer.runRight, SubsequentialTransducer.run,
          plateauRight_runFrom_low, plateauRight_runFrom_faithful, plateauRight_runFrom_plateau,
          ← replicate_succ]

/-- First-last plateauing is weakly deterministic in Heinz and Lai's sense: a left-to-right pass
moves the first unit to the end of the word, where the right-to-left pass reads it first. -/
theorem firstLast_isWeaklyDeterministic : IsWeaklyDeterministic firstLast :=
  (funext firstLast_eq_plateau_rotate :
      firstLast = plateauRight.runRight ∘ fun w ↦ w.rotate 1) ▸
    plateauRight.isRightSubsequential.isWeaklyDeterministic_comp_rotate

/-! ### Double-edged spread -/

/-- In double-edged spread a unit surfaces H when it is H, or when the word has an H and none
before the unit or none after it: the first H spreads to the left edge and the last to the right
edge. -/
def doubleEdged.Surfaces (w : List AssociationState) (i : ℕ) : Prop :=
  w[i]? = some .H ∨ .H ∈ w ∧ (.H ∉ w.take i ∨ .H ∉ w.drop (i + 1))

instance (w : List AssociationState) (i : ℕ) : Decidable (doubleEdged.Surfaces w i) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Double-edged spread writes H at the units that surface H and L at the others. -/
def doubleEdged (w : List AssociationState) : List AssociationState :=
  w.mapIdx fun i _ ↦ if doubleEdged.Surfaces w i then .H else .O

example : doubleEdged [.O, .O, .O, .H, .O, .O, .H, .O, .O, .H, .O, .O, .O]
    = [.H, .H, .H, .H, .O, .O, .H, .O, .O, .H, .H, .H, .H] ∧
    doubleEdged [.O, .O, .O, .O] = [.O, .O, .O, .O] := by
  decide

theorem getElem?_doubleEdged (w : List AssociationState) (i : ℕ) :
    (doubleEdged w)[i]? = w[i]?.map fun _ ↦
      if doubleEdged.Surfaces w i then AssociationState.H else AssociationState.O := by
  simp [doubleEdged, getElem?_mapIdx]

/-- Double-edged spread is unbounded circumambient: a toneless unit before the only H of a word
surfaces H, and an H added far to its left, or the H far to its right removed, leaves it
toneless. -/
theorem doubleEdged_isUnboundedCircumambient : IsUnboundedCircumambient doubleEdged :=
  .of_flanks (fill := .O) (xOn := .O) (yOn := .H) (xOff := .H) (yOff := .O)
    (n := fun d ↦ 2 * d + 2) (t := fun d ↦ d + 1) (fun d ↦ by omega) (fun d ↦ by omega)
    (fun d ↦ by
      rw [getElem?_doubleEdged, getElem?_flankWord_mid (by omega) (by omega), Option.map_some,
        ite_eq_left (.inr ⟨by simp [flankWord], .inl fun h ↦
          absurd ((mem_take_flankWord_iff (by decide) (by omega)).mp h) (by decide)⟩)]
      decide)
    (fun d ↦ by
      rw [getElem?_doubleEdged, getElem?_flankWord_mid (by omega) (by omega), Option.map_some,
        ite_eq_right]
      rintro (h | ⟨-, h | h⟩)
      · rw [getElem?_flankWord_mid (by omega) (by omega)] at h
        exact absurd h (by decide)
      · exact h ((mem_take_flankWord_iff (by decide) (by omega)).mpr rfl)
      · exact h ((mem_drop_flankWord_iff (by decide) (by omega)).mpr rfl))
    (fun d ↦ by
      rw [getElem?_doubleEdged, getElem?_flankWord_mid (by omega) (by omega), Option.map_some,
        ite_eq_right]
      rintro (h | ⟨h, -⟩)
      · rw [getElem?_flankWord_mid (by omega) (by omega)] at h
        exact absurd h (by decide)
      · simp [flankWord] at h)

/-- The left-to-right pass that writes H until it has read an H and copies afterwards: the first
H of a word spreads to its left edge, and a word without an H becomes all H. -/
def spread : Mealy Bool AssociationState AssociationState :=
  .ofFlag (fun a ↦ decide (a = .H)) fun b a ↦ if b then a else .H

private theorem spread_runFrom_true (w : List AssociationState) : spread.runFrom true w = w := by
  induction w with
  | nil => rfl
  | cons a w ih => exact congrArg (a :: ·) ih

private theorem spread_run_H (w : List AssociationState) : spread.run (.H :: w) = .H :: w :=
  congrArg (AssociationState.H :: ·) (spread_runFrom_true w)

private theorem spread_run_O (w : List AssociationState) :
    spread.run (.O :: w) = .H :: spread.run w :=
  rfl

private theorem getElem?_spread_run (w : List AssociationState) (i : ℕ) :
    (spread.run w)[i]? = w[i]?.map fun a ↦ if .H ∈ w.take i then a else .H := by
  simp [spread, Mealy.getElem?_ofFlag_run]

private theorem getElem?_spread_runRight (w : List AssociationState) (i : ℕ) :
    (spread.runRight w)[i]? = w[i]?.map fun a ↦ if .H ∈ w.drop (i + 1) then a else .H := by
  simp [spread, Mealy.getElem?_ofFlag_runRight]

private theorem spread_run_append_H (v r : List AssociationState) :
    spread.run (v ++ .H :: r) = spread.run v ++ .H :: r := by
  induction v with
  | nil => exact spread_run_H r
  | cons a v ih => cases a <;> simp [spread_run_H, spread_run_O, ih]

private theorem mem_drop_spread_run {w : List AssociationState} (h : .H ∈ w) (j : ℕ) :
    .H ∈ (spread.run w).drop j ↔ .H ∈ w.drop j := by
  induction w generalizing j with
  | nil => simp at h
  | cons a w ih =>
    cases a with
    | H => rw [spread_run_H]
    | O =>
      have hw : .H ∈ w := by simpa using h
      cases j with
      | zero => simp [spread_run_O, hw]
      | succ j => simpa [spread_run_O] using ih hw j

theorem doubleEdged_eq (w : List AssociationState) :
    doubleEdged w = if .H ∈ w then spread.runRight (spread.run w) else w := by
  refine ext_getElem? fun i ↦ ?_
  split_ifs with h <;> rw [getElem?_doubleEdged]
  · simp only [getElem?_spread_runRight, getElem?_spread_run, mem_drop_spread_run h]
    rcases h' : w[i]? with _ | a
    · simp
    · cases a <;> by_cases h₁ : .H ∈ w.take i <;> by_cases h₂ : .H ∈ w.drop (i + 1) <;>
        simp [doubleEdged.Surfaces, h, h', h₁, h₂]
  · rcases h' : w[i]? with _ | a
    · simp
    · cases a
      · exact absurd (mem_of_getElem? h') h
      · simp [doubleEdged.Surfaces, h, h']

/-- The first pass starts before the first unit, is `toneless` having read only Ls, and `toned`
after an H. -/
inductive EdgeState
  | start | toneless | toned
  deriving DecidableEq, Repr, Fintype

/-- The transitions of the first pass. -/
@[simp] def edgeStep : EdgeState → AssociationState → EdgeState
  | .start, .H => .toned | .start, .O => .toneless
  | .toneless, .H => .toned | .toneless, .O => .toneless
  | .toned, _ => .toned

/-- The first pass writes nothing for the first unit, H for every other unit up to the first H,
and copies the rest. -/
@[simp] def edgeOutput : EdgeState → AssociationState → List AssociationState
  | .start, _ => []
  | .toneless, _ => [.H]
  | .toned, a => [a]

/-- At the end of the word the first pass writes whether the word had an H. -/
@[simp] def edgeFinal : EdgeState → List AssociationState
  | .start => []
  | .toneless => [.O]
  | .toned => [.H]

/-- The left-to-right pass that spreads the first H leftward, drops the first unit, and ends the
word with an H exactly when it had one. -/
@[simps]
def spreadEdge : SubsequentialTransducer EdgeState AssociationState AssociationState where
  start := .start
  step := edgeStep
  output := edgeOutput
  finalOutput := edgeFinal

private theorem spreadEdge_runFrom_toned (w : List AssociationState) :
    spreadEdge.runFrom .toned w = w ++ [.H] := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

private theorem spreadEdge_runFrom_toneless (w : List AssociationState) :
    spreadEdge.runFrom .toneless w = spread.run w ++ [if .H ∈ w then .H else .O] := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [spread_run_H, spread_run_O, ih, spreadEdge_runFrom_toned]

private theorem spreadEdge_run_cons (a : AssociationState) (w : List AssociationState) :
    spreadEdge.run (a :: w)
      = (spread.run (a :: w)).tail ++ [if .H ∈ a :: w then .H else .O] := by
  cases a <;>
    simp [SubsequentialTransducer.run, spread_run_H, spread_run_O, spreadEdge_runFrom_toned,
      spreadEdge_runFrom_toneless]

theorem length_spreadEdge_run (w : List AssociationState) :
    (spreadEdge.run w).length = w.length := by
  rcases w with _ | ⟨a, w⟩
  · rfl
  · simp [spreadEdge_run_cons]

/-- Reading right to left, the second pass starts before the last unit, is `toneless` when that
unit says the word has no H, is `spread` up to the last H of the word, and `copy` after it. -/
inductive CloseState
  | start | toneless | spread | copy
  deriving DecidableEq, Repr, Fintype

/-- The transitions of the second pass. -/
@[simp] def closeStep : CloseState → AssociationState → CloseState
  | .start, .H => .spread | .start, .O => .toneless
  | .toneless, _ => .toneless
  | .spread, .H => .copy | .spread, .O => .spread
  | .copy, _ => .copy

/-- The second pass writes nothing for the last unit, L throughout a word without an H, and
otherwise H up to the last H of the word and a copy after it. -/
@[simp] def closeOutput : CloseState → AssociationState → List AssociationState
  | .start, _ => []
  | .toneless, _ => [.O]
  | .spread, _ => [.H]
  | .copy, a => [a]

/-- At the end of the word the second pass writes the dropped first unit back. -/
@[simp] def closeFinal : CloseState → List AssociationState
  | .start => []
  | .toneless => [.O]
  | _ => [.H]

/-- The right-to-left pass that spreads the last H rightward and restores the first unit, as run
by `runRight`. -/
@[simps]
def closeRight : SubsequentialTransducer CloseState AssociationState AssociationState where
  start := .start
  step := closeStep
  output := closeOutput
  finalOutput := closeFinal

private theorem closeRight_runFrom_toneless (w : List AssociationState) :
    closeRight.runFrom .toneless w = replicate (w.length + 1) .O := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih, replicate_succ]

private theorem closeRight_runFrom_copy (w : List AssociationState) :
    closeRight.runFrom .copy w = w ++ [.H] := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

private theorem closeRight_runFrom_spread (w : List AssociationState) :
    closeRight.runFrom .spread w = spread.run w ++ [.H] := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [spread_run_H, spread_run_O, ih, closeRight_runFrom_copy]

private theorem closeRight_runRight_concat_O (w : List AssociationState) :
    closeRight.runRight (w ++ [.O]) = replicate (w.length + 1) .O := by
  simp [SubsequentialTransducer.runRight, SubsequentialTransducer.run,
    closeRight_runFrom_toneless]

private theorem closeRight_runRight_concat_H (w : List AssociationState) :
    closeRight.runRight (w ++ [.H]) = .H :: spread.runRight w := by
  simp [SubsequentialTransducer.runRight, SubsequentialTransducer.run,
    closeRight_runFrom_spread, Mealy.runRight]

theorem doubleEdged_eq_close_spread (w : List AssociationState) :
    doubleEdged w = closeRight.runRight (spreadEdge.run w) := by
  rcases w with _ | ⟨a, w⟩
  · decide
  · rw [doubleEdged_eq, spreadEdge_run_cons]
    split_ifs with h
    · rw [closeRight_runRight_concat_H]
      cases a <;> simp [spread_run_H, spread_run_O, Mealy.runRight, spread_run_append_H _ []]
    · rw [closeRight_runRight_concat_O, length_tail, Mealy.length_run]
      exact eq_replicate_O_iff.mpr h

/-- Double-edged spread is weakly deterministic in Heinz and Lai's sense: a left-to-right pass
spreads the first H and ends the word with a record of whether it had one, and the right-to-left
pass spreads the last H. -/
theorem doubleEdged_isWeaklyDeterministic : IsWeaklyDeterministic doubleEdged :=
  ⟨spreadEdge.run, closeRight.runRight, spreadEdge.isLeftSubsequential,
    fun w ↦ (length_spreadEdge_run w).le, closeRight.isRightSubsequential,
    funext fun w ↦ (doubleEdged_eq_close_spread w).symm⟩

end LamontOHaraSmith2019
