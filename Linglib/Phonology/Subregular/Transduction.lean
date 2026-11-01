/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.Docking
public import Linglib.Phonology.Subregular.ISL
public import Mathlib.Data.List.Find

/-!
# Quantifier-free logical transductions

A **logical transduction** defines an output string inside its input: a fixed number of copies
of each input position, and for each copy formulas over the input saying which output symbol, if
any, the copy carries. It is **quantifier-free** when those formulas are, and a quantifier-free
formula at a position is a `Subregular.StringFormula` of the string model, reading a bounded
window through the successor and predecessor functions. Chandlee and Jardine report that the
quantifier-free string transductions are exactly the input strictly local functions. This file
proves the one-sided case: over a finite alphabet, the transductions whose guards read only
backward compute exactly the left input strictly local functions.

The transductions here are **order-preserving** in the sense of [dolatian-2020] (§7.4.2): the
output is read off in the order (input position, copy), so the output successor is induced
rather than defined by formulas of its own. Transductions that define it, such as
[dolatian-2020]'s iconic reduplication, are not represented.

## Main definitions

* `Subregular.Transduction`: a decision list of guarded clauses, each emitting a block.
* `Transduction.apply`: the output string, computably.
* `Transduction.LeftLocal r`: every guard reads at most `r` positions back and none forward.
* `ISLRule.toTransduction`: the left-local transduction with a clause for each window and
  symbol, guarded by `StringFormula.window`.
* `Transduction.relabel`: the relabelling transduction of a quantifier-free docking process over
  a finite alphabet.

## Main results

* `Transduction.LeftLocal.emitAt_congr`: a left-local transduction emits the same block at
  positions whose bounded left contexts agree.
* `Transduction.LeftLocal.isLeftInputStrictlyLocal`: a transduction left-local with radius `r` is
  `(r + 1)`-left input strictly local.
* `ISLRule.apply_toTransduction`: on words over the alphabet, the transduction of an ISL rule
  computes it.
* `isLeftInputStrictlyLocal_iff_exists_leftLocal`: over a finite alphabet, the
  `(r + 1)`-left input strictly local functions are those of the transductions left-local with
  radius `r`.
* `Transduction.apply_relabel`: on words over the alphabet, the relabelling transduction of a
  quantifier-free docking process computes its map.

## Implementation notes

The copy set is folded into the clauses: a clause emits the block of symbols that the copies of
its position carry, in copy order, so a copy set of size `k` bounds the blocks by `k`, an empty
block deletes, and a longer one inserts. The clauses form a decision list, the first whose guard
holds firing. The literature's formula for symbol `b` on copy `c` is the disjunction, over the
clauses whose block has `b` at `c`, of the clause's guard with the negations of the guards before
it; the decision list keeps the output functional by construction and lets `apply` reduce under
`decide`.

The characterization is one-sided because `ISLRule` carries no final output, so a rule scanning
left to right cannot wait for the input after a position; guards that read forward fall outside
it. `ISLRule.toTransduction` is not economical, with a clause for every window and symbol; the
characterization needs only that it exists.

## References

* [chandlee-2014]
* [chandlee-jardine-2019]
* [dolatian-2020]
-/

@[expose] public section

namespace Subregular

variable {α β : Type*}

/-- A quantifier-free order-preserving logical transduction is a decision list of clauses: a
quantifier-free guard at the input position, paired with the block of output symbols the
position yields when that clause is the first to hold. -/
structure Transduction (α β : Type*) where
  /-- The guarded clauses, in order of precedence. -/
  clauses : List (StringFormula α × List β)

namespace Transduction

variable (T : Transduction α β)

/-- A transduction is **left-local** with radius `r` if every guard is bounded by `r` back and
nothing forward, reading only its position and the `r` positions before it. -/
def LeftLocal (r : ℕ) : Prop :=
  ∀ cl ∈ T.clauses, StringFormula.Bounded r 0 cl.1

variable [DecidableEq α]

/-- The block emitted at input position `n`: that of the first clause whose guard holds there,
or nothing. -/
def emitAt (w : List α) (n : ℕ) : List β :=
  ((T.clauses.find? fun cl ↦ cl.1.HoldsAt w n).map Prod.snd).getD []

/-- The output string: the blocks emitted at the input positions, left to right. -/
def apply (w : List α) : List β :=
  (List.range w.length).flatMap (T.emitAt w)

@[simp] theorem apply_nil : T.apply [] = [] := rfl

variable {T} {w : List α} {n : ℕ}

theorem emitAt_eq_of_mem {cl : StringFormula α × List β} (hcl : cl ∈ T.clauses)
    (h : cl.1.HoldsAt w n) (huniq : ∀ cl' ∈ T.clauses, cl'.1.HoldsAt w n → cl'.2 = cl.2) :
    T.emitAt w n = cl.2 := by
  obtain ⟨cl', hcl'⟩ := Option.isSome_iff_exists.1 <|
    (List.find?_isSome (p := fun cl : StringFormula α × List β ↦ decide (cl.1.HoldsAt w n))).2
      ⟨cl, hcl, decide_eq_true h⟩
  rw [emitAt, hcl', Option.map_some, Option.getD_some,
    huniq _ (List.mem_of_find?_eq_some hcl') (by simpa using List.find?_some hcl')]

/-! ### Left-local transductions are input strictly local -/

namespace LeftLocal

variable {r : ℕ} (hT : T.LeftLocal r)
include hT

/-- A left-local transduction emits the same block at positions whose bounded left contexts
agree. -/
theorem emitAt_congr {w w' : List α} {n n' : ℕ} (hedge : min n r = min n' r)
    (hlbl : ∀ j ≤ r, w[n - j]? = w'[n' - j]?) : T.emitAt w n = T.emitAt w' n' :=
  congrArg (fun o ↦ (o.map Prod.snd).getD []) <| List.find?_congr fun cl hcl ↦
    decide_eq_decide.2 <| (hT cl hcl).holdsAt_congr hedge hlbl fun j hj ↦ by
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      simpa using hlbl 0 (Nat.zero_le r)

theorem emitAt_append {u : List α} (v : List α) {p : ℕ} (hp : p < u.length) :
    T.emitAt (u ++ v) p = T.emitAt u p :=
  hT.emitAt_congr rfl fun _ _ ↦ List.getElem?_append_left (by omega)

theorem emitAt_eq_emitAt_rtake {w : List α} {p : ℕ} (hp : p < w.length) :
    T.emitAt w p = T.emitAt ((w.take (p + 1)).rtake (r + 1)) (min r p) := by
  have hlen : (w.take (p + 1)).length = p + 1 := by simp; omega
  refine hT.emitAt_congr (by omega) fun j hj ↦ ?_
  rw [List.getElem?_rtake, hlen, List.getElem?_take, ite_eq_left (by omega)]
  congr 1
  omega

theorem apply_append_singleton (u : List α) (x : α) :
    T.apply (u ++ [x]) = T.apply u ++ T.emitAt (u ++ [x]) u.length := by
  rw [apply, List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
    List.flatMap_singleton, apply, List.flatMap_congr fun p hp ↦
      hT.emitAt_append [x] (List.mem_range.1 hp)]

/-- A transduction left-local with radius `r` is `(r + 1)`-left input strictly local: the rule
emitting, after a window of `r` symbols, the block the transduction emits at the end of the
window followed by the symbol computes it. -/
theorem isLeftInputStrictlyLocal : IsLeftInputStrictlyLocal (r + 1) T.apply := by
  refine ⟨⟨fun window x ↦ T.emitAt (window ++ [x]) window.length⟩, funext fun w ↦ ?_⟩
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton u x ih =>
    rw [ISLRule.apply_append_singleton, ih, hT.apply_append_singleton,
      hT.emitAt_eq_emitAt_rtake (by simp), List.take_of_length_le (by simp),
      List.rtake_concat_succ, Nat.add_sub_cancel, ← List.length_rtake]

end LeftLocal

end Transduction

/-! ### Input strictly local functions are left-local transductions -/

namespace ISLRule

/-- The words over `alphabet` of length at most `r`, the windows a `(r + 1)`-ISL rule reads. -/
def windows (alphabet : List α) : ℕ → List (List α)
  | 0 => [[]]
  | r + 1 => [] :: (windows alphabet r).flatMap fun u ↦ alphabet.map (· :: u)

theorem mem_windows {alphabet u : List α} {r : ℕ} :
    u ∈ windows alphabet r ↔ u.length ≤ r ∧ ∀ a ∈ u, a ∈ alphabet := by
  induction r generalizing u with
  | zero =>
    simp only [windows, List.mem_singleton, Nat.le_zero, List.length_eq_zero_iff]
    exact ⟨fun h ↦ ⟨h, by simp [h]⟩, And.left⟩
  | succ r ih =>
    cases u with
    | nil => simp [windows]
    | cons a u => simp [windows, ih, and_comm, and_left_comm]

variable {r : ℕ} (ρ : ISLRule (r + 1) α β) (alphabet : List α)

/-- The transduction of a `(r + 1)`-ISL rule over the symbols `alphabet`: under the guard that the
position carries `a` after the window `u`, the block the rule emits there. -/
def toTransduction : Transduction α β :=
  ⟨(windows alphabet r).flatMap fun u ↦ alphabet.map fun a ↦
    (StringFormula.label a (.var 0) ⊓ StringFormula.window r u, ρ.windowOutput u a)⟩

theorem leftLocal_toTransduction : (ρ.toTransduction alphabet).LeftLocal r := by
  intro cl hcl
  simp only [toTransduction, List.mem_flatMap, List.mem_map] at hcl
  obtain ⟨u, hu, a, -, rfl⟩ := hcl
  rw [StringFormula.bounded_inf, StringFormula.bounded_label]
  exact ⟨⟨Nat.zero_le r, le_rfl⟩, StringFormula.bounded_window (mem_windows.1 hu).1⟩

variable [DecidableEq α]

theorem emitAt_toTransduction {w : List α} (hw : ∀ a ∈ w, a ∈ alphabet) {p : ℕ}
    (hp : p < w.length) :
    (ρ.toTransduction alphabet).emitAt w p = ρ.windowOutput ((w.take p).rtake r) w[p] := by
  have hguard {u : List α} (hu : u ∈ windows alphabet r) (a : α) :
      (StringFormula.label a (.var 0) ⊓ StringFormula.window r u).HoldsAt w p ↔
        w[p] = a ∧ (w.take p).rtake r = u := by
    rw [StringFormula.holdsAt_inf, StringFormula.holdsAt_label_var,
      StringFormula.holdsAt_window hp (mem_windows.1 hu).1, List.getElem?_eq_getElem hp,
      Option.some.injEq]
  have hwin : (w.take p).rtake r ∈ windows alphabet r :=
    mem_windows.2 ⟨List.length_rtake_le r _, fun a ha ↦
      hw a (List.mem_of_mem_take ((List.rtake_suffix r _).subset ha))⟩
  have hmem {cl} : cl ∈ (ρ.toTransduction alphabet).clauses ↔ ∃ u ∈ windows alphabet r,
      ∃ a ∈ alphabet,
        (StringFormula.label a (.var 0) ⊓ StringFormula.window r u, ρ.windowOutput u a) = cl :=
    by simp [toTransduction]
  refine Transduction.emitAt_eq_of_mem (hmem.2 ⟨_, hwin, w[p], hw _ (List.getElem_mem hp), rfl⟩)
    ((hguard hwin _).2 ⟨rfl, rfl⟩) fun cl hcl h ↦ ?_
  obtain ⟨u, hu, a, -, rfl⟩ := hmem.1 hcl
  obtain ⟨rfl, rfl⟩ := (hguard hu a).1 h
  rfl

/-- Over the alphabet, the transduction of an ISL rule computes the rule. -/
theorem apply_toTransduction {w : List α} (hw : ∀ a ∈ w, a ∈ alphabet) :
    (ρ.toTransduction alphabet).apply w = ρ.apply w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton u x ih =>
    rw [(ρ.leftLocal_toTransduction alphabet).apply_append_singleton,
      ih fun a ha ↦ hw a (List.mem_append_left _ ha),
      ρ.emitAt_toTransduction alphabet hw (by simp), ISLRule.apply_append_singleton]
    simp

end ISLRule

/-- Over a finite alphabet, the `(r + 1)`-left input strictly local functions are exactly the
functions of the transductions left-local with radius `r`. -/
theorem isLeftInputStrictlyLocal_iff_exists_leftLocal [DecidableEq α] [Fintype α] {r : ℕ}
    {f : List α → List β} :
    IsLeftInputStrictlyLocal (r + 1) f ↔ ∃ T : Transduction α β, T.LeftLocal r ∧ T.apply = f := by
  refine ⟨fun ⟨ρ, hρ⟩ ↦ ⟨ρ.toTransduction Finset.univ.toList, ρ.leftLocal_toTransduction _,
    funext fun w ↦ ?_⟩, fun ⟨T, hT, hf⟩ ↦ hf ▸ hT.isLeftInputStrictlyLocal⟩
  rw [ρ.apply_toTransduction _ fun a _ ↦ Finset.mem_toList.2 (Finset.mem_univ a), hρ]

namespace Transduction

/-! ### Relabelling transductions -/

/-- The relabelling transduction of the quantifier-free docking process with guard `φ` over the
symbols `alphabet`: each symbol is docked where the guard holds and kept elsewhere. -/
def relabel (φ : StringFormula α) (dock : α → α) (alphabet : List α) : Transduction α α :=
  ⟨alphabet.flatMap fun a ↦
    [(φ ⊓ StringFormula.label a (.var 0), [dock a]),
      (φ.not ⊓ StringFormula.label a (.var 0), [a])]⟩

variable [DecidableEq α]

private theorem flatMap_range_toList_eq_mapIdx {γ δ : Type*} (f : ℕ → γ → δ) :
    ∀ w : List γ, (List.range w.length).flatMap (fun n ↦ (w[n]?.map (f n)).toList) = w.mapIdx f
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.mapIdx_cons, ← flatMap_range_toList_eq_mapIdx (fun i ↦ f (i + 1)) l]
    simp

/-- On a word over the alphabet, the relabelling transduction computes the docking map. -/
theorem apply_relabel {φ : StringFormula α} {dock : α → α} {alphabet : List α} {w : List α}
    (hw : ∀ a ∈ w, a ∈ alphabet) :
    (relabel φ dock alphabet).apply w = (Docking.ofQF φ dock).map w := by
  have hmem {cl} : cl ∈ (relabel φ dock alphabet).clauses ↔ ∃ a ∈ alphabet,
      cl = (φ ⊓ StringFormula.label a (.var 0), [dock a]) ∨
        cl = (φ.not ⊓ StringFormula.label a (.var 0), [a]) := by
    simp [relabel]
  have hemit {n : ℕ} (hn : n < w.length) : (relabel φ dock alphabet).emitAt w n =
      (w[n]?.map fun a ↦ if φ.HoldsAt w n then dock a else a).toList := by
    simp only [List.getElem?_eq_getElem hn, Option.map_some, Option.toList_some]
    refine emitAt_eq_of_mem
      (cl := ((if φ.HoldsAt w n then φ else φ.not) ⊓ StringFormula.label w[n] (.var 0),
        [if φ.HoldsAt w n then dock w[n] else w[n]])) (hmem.2 ⟨_, hw _ (List.getElem_mem hn), ?_⟩)
      (by split_ifs <;> simp [*]) fun cl hcl h ↦ ?_
    · split_ifs <;> simp
    · obtain ⟨a, -, rfl | rfl⟩ := hmem.1 hcl <;> simp_all
  rw [apply, List.flatMap_congr fun n hn ↦ hemit (List.mem_range.1 hn),
    flatMap_range_toList_eq_mapIdx]
  rfl

end Transduction

end Subregular
