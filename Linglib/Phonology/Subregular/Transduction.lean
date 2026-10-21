/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.Docking
public import Linglib.Phonology.Subregular.ISL
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.List.Find

/-!
# Quantifier-free logical transductions

A **logical transduction** defines an output string inside its input: a fixed number of copies
of each input position, and for each copy formulas over the input saying which output symbol, if
any, the copy carries. It is **quantifier-free** when those formulas are, and a quantifier-free
formula at a position is a `Subregular.WindowFormula`, reading a bounded window through
successor and predecessor steps. A second copy inserts, a copy none of whose formulas hold
deletes, and a formula emitting another symbol rewrites in place. [chandlee-jardine-2019] report
that the quantifier-free string transductions are exactly the input strictly local functions.
This file proves the one-sided case: over a finite alphabet, the transductions whose guards read
only backward compute exactly the left input strictly local functions.

The transductions here are **order-preserving** in the sense of [dolatian-2020] (§7.4.2): the
output is read off in the order (input position, copy), so the output successor is induced
rather than defined by formulas of its own. Transductions that define it, such as
[dolatian-2020]'s iconic reduplication, are not represented.

## Main definitions

* `Subregular.Transduction`: a copy count and, per copy, a decision list of guarded clauses.
* `Transduction.apply`: the output string, computably.
* `Transduction.LeftLocal r`: every guard reads at most `r` positions back and none forward.
* `Transduction.toISLRule`: the ISL rule that runs a transduction on each window.
* `ISLRule.toTransduction`: the left-local transduction with a clause for each window and
  symbol, guarded by `WindowFormula.window`.
* `Transduction.relabel`: the one-copy relabelling transduction of a quantifier-free docking
  process over a finite alphabet.

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

The clauses of a copy form a decision list: the first clause whose guard holds fires, and a copy
with no firing clause is absent. The literature's formula for an output symbol `b` on a copy is
the disjunction, over the copy's clauses emitting `b`, of the clause's guard with the negations
of the guards before it; the decision list keeps the output functional by construction and
lets `apply` reduce under `decide`.

The characterization is one-sided because `ISLRule` carries no final output, so a rule scanning
left to right cannot wait for the input after a position; guards that read forward fall outside
it. `ISLRule.toTransduction` is not economical, with a clause for every window and symbol and as
many copies as all its blocks have symbols together; the characterization needs only that it
exists.

## References

* [chandlee-2014]
* [chandlee-jardine-2019]
* [dolatian-2020]
-/

@[expose] public section

namespace Subregular

variable {α β : Type*}

/-- A quantifier-free order-preserving logical transduction has `copies` output copies of each
input position and, for each copy, a decision list of clauses: a quantifier-free guard at the
input position, paired with the symbol the copy carries when that clause is the first to hold. -/
structure Transduction (α β : Type*) where
  /-- The number of output copies of each input position. -/
  copies : ℕ
  /-- The guarded clauses of each copy, in order of precedence. -/
  clauses : Fin copies → List (WindowFormula α × β)

namespace Transduction

variable (T : Transduction α β)

/-- A transduction is **left-local** with radius `r` if every guard is backward-bounded by `r`,
reading only its position and the `r` positions before it. -/
def LeftLocal (r : ℕ) : Prop :=
  ∀ c, ∀ cl ∈ T.clauses c, cl.1.BackBounded r

instance (r : ℕ) : Decidable (T.LeftLocal r) :=
  inferInstanceAs (Decidable (∀ c, ∀ cl ∈ T.clauses c, cl.1.BackBounded r))

variable [DecidableEq α]

/-- The block emitted at input position `n`: for each copy in order, the symbol of the first
clause whose guard holds at `n`, if any. -/
def emitAt (w : List α) (n : ℕ) : List β :=
  (List.finRange T.copies).filterMap fun c ↦
    ((T.clauses c).find? fun cl ↦ cl.1.Realize w n).map Prod.snd

/-- The output string: the blocks emitted at the input positions, left to right. -/
def apply (w : List α) : List β :=
  (List.range w.length).flatMap (T.emitAt w)

@[simp] theorem apply_nil : T.apply [] = [] := rfl

/-- The `(r + 1)`-ISL rule that emits, for a symbol after a window of `r` symbols, the block the
transduction emits at the end of the window followed by the symbol. -/
def toISLRule (r : ℕ) : ISLRule (r + 1) α β where
  windowOutput window x := T.emitAt (window ++ [x]) window.length

/-! ### Left-local transductions are input strictly local -/

namespace LeftLocal

variable {T} {r : ℕ} (hT : T.LeftLocal r)
include hT

/-- A left-local transduction emits the same block at positions whose bounded left contexts
agree. -/
theorem emitAt_congr {w w' : List α} {n n' : ℕ} (hn : n < w.length) (hn' : n' < w'.length)
    (hlbl : ∀ j ≤ r, w[n - j]? = w'[n' - j]?) (hedge : ∀ j ≤ r, (j ≤ n ↔ j ≤ n')) :
    T.emitAt w n = T.emitAt w' n' :=
  List.filterMap_congr fun c _ ↦ congrArg _ <| List.find?_congr fun cl hcl ↦
    decide_eq_decide.2 <| WindowFormula.BackBounded.realize_congr hn hn' hlbl hedge (hT c cl hcl)

/-- Extending the input leaves a left-local transduction's blocks at the old positions. -/
theorem emitAt_append {u : List α} (v : List α) {p : ℕ} (hp : p < u.length) :
    T.emitAt (u ++ v) p = T.emitAt u p :=
  hT.emitAt_congr (by simp; omega) hp (fun _ _ ↦ List.getElem?_append_left (by omega))
    fun _ _ ↦ Iff.rfl

/-- The block a left-local transduction emits at position `p` is the block it emits at the end
of the `r + 1` input symbols ending at `p`. -/
theorem emitAt_eq_emitAt_rtake {w : List α} {p : ℕ} (hp : p < w.length) :
    T.emitAt w p = T.emitAt ((w.take (p + 1)).rtake (r + 1)) (min r p) := by
  have hlen : (w.take (p + 1)).length = p + 1 := by simp; omega
  refine hT.emitAt_congr hp (by simp [hlen]) (fun j hj ↦ ?_) fun _ _ ↦ by omega
  rw [List.getElem?_rtake, hlen, List.getElem?_take, ite_eq_left (by omega)]
  congr 1
  omega

/-- Appending a symbol to the input of a left-local transduction appends the block at its
end. -/
theorem apply_append_singleton (u : List α) (x : α) :
    T.apply (u ++ [x]) = T.apply u ++ T.emitAt (u ++ [x]) u.length := by
  rw [apply, List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
    List.flatMap_singleton, apply, List.flatMap_congr fun p hp ↦
      hT.emitAt_append [x] (List.mem_range.1 hp)]

/-- The ISL rule of a left-local transduction computes it. -/
theorem toISLRule_apply : (T.toISLRule r).apply = T.apply := by
  funext w
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton u x ih =>
    rw [ISLRule.apply_append_singleton, ih, hT.apply_append_singleton,
      hT.emitAt_eq_emitAt_rtake (by simp), List.take_of_length_le (by simp),
      List.rtake_concat_succ, Nat.add_sub_cancel, ← List.length_rtake]
    rfl

/-- A transduction left-local with radius `r` is `(r + 1)`-left input strictly local. -/
theorem isLeftInputStrictlyLocal : IsLeftInputStrictlyLocal (r + 1) T.apply :=
  ⟨T.toISLRule r, hT.toISLRule_apply⟩

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

/-- The transduction of a `(r + 1)`-ISL rule over the symbols `alphabet`: copy `c` carries, under
the guard that the position carries `a` after the window `u`, the `c`-th symbol of the block the
rule emits there. There are copies enough for every block. -/
def toTransduction : Transduction α β where
  copies := ((windows alphabet r).flatMap fun u ↦
    alphabet.map fun a ↦ (ρ.windowOutput u a).length).sum
  clauses c := (windows alphabet r).flatMap fun u ↦ alphabet.filterMap fun a ↦
    (ρ.windowOutput u a)[c.val]?.map ((WindowFormula.label a .var).conj (.window r u), ·)

theorem leftLocal_toTransduction : (ρ.toTransduction alphabet).LeftLocal r := by
  intro c cl hcl
  simp only [toTransduction, List.mem_flatMap, List.mem_filterMap, Option.map_eq_some_iff] at hcl
  obtain ⟨u, hu, a, -, b, -, rfl⟩ := hcl
  exact ⟨⟨Nat.zero_le r, le_rfl⟩, WindowFormula.window_backBounded
    (mem_windows.1 hu).1⟩

variable [DecidableEq α]

private theorem filterMap_finRange_getElem? {γ : Type*} :
    ∀ {l : List γ} {N : ℕ}, l.length ≤ N → (List.finRange N).filterMap (fun c ↦ l[c.val]?) = l
  | [], _, _ => by simp
  | b :: l, N + 1, h => by
    simp [List.finRange_succ, List.filterMap_map,
      filterMap_finRange_getElem? (l := l) (N := N) (by simpa using h)]

/-- At an in-range position of a word over the alphabet, the transduction of an ISL rule emits the
block the rule emits after the window there. -/
theorem emitAt_toTransduction {w : List α} (hw : ∀ a ∈ w, a ∈ alphabet) {p : ℕ}
    (hp : p < w.length) :
    (ρ.toTransduction alphabet).emitAt w p = ρ.windowOutput ((w.take p).rtake r) w[p] := by
  have hwin : (w.take p).rtake r ∈ windows alphabet r :=
    mem_windows.2 ⟨List.length_rtake_le r _, fun a ha ↦
      hw a (List.mem_of_mem_take ((List.rtake_suffix r _).subset ha))⟩
  have hguard {u : List α} (hu : u ∈ windows alphabet r) (a : α) :
      ((WindowFormula.label a .var).conj (.window r u)).Realize w p ↔
        w[p] = a ∧ (w.take p).rtake r = u := by
    rw [WindowFormula.realize_conj, WindowFormula.realize_label_var,
      WindowFormula.realize_window hp (mem_windows.1 hu).1, List.getElem?_eq_getElem hp,
      Option.some.injEq]
  have hcopy (c : Fin (ρ.toTransduction alphabet).copies) :
      (((ρ.toTransduction alphabet).clauses c).find? fun cl ↦ cl.1.Realize w p).map Prod.snd =
        (ρ.windowOutput ((w.take p).rtake r) w[p])[c.val]? := by
    have hmem {cl} : cl ∈ (ρ.toTransduction alphabet).clauses c ↔ ∃ u ∈ windows alphabet r,
        ∃ a ∈ alphabet, ∃ b, (ρ.windowOutput u a)[c.val]? = some b ∧
          ((WindowFormula.label a .var).conj (.window r u), b) = cl := by
      simp [toTransduction]
    have hfound {cl} (hcl : ((ρ.toTransduction alphabet).clauses c).find?
        (fun cl ↦ cl.1.Realize w p) = some cl) :
        (ρ.windowOutput ((w.take p).rtake r) w[p])[c.val]? = some cl.2 := by
      obtain ⟨u, hu, a, -, b, hb, rfl⟩ := hmem.1 (List.mem_of_find?_eq_some hcl)
      obtain ⟨rfl, rfl⟩ := (hguard hu a).1 (by simpa using List.find?_some hcl)
      exact hb
    refine Option.ext fun b ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨cl, hcl, rfl⟩ := Option.map_eq_some_iff.1 h
      exact hfound hcl
    · obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.1 <|
        (List.find?_isSome (p := fun cl : WindowFormula α × β ↦ decide (cl.1.Realize w p))).2
          ⟨_, hmem.2 ⟨_, hwin, w[p], hw _ (List.getElem_mem hp), b, h, rfl⟩,
            decide_eq_true ((hguard hwin w[p]).2 ⟨rfl, rfl⟩)⟩
      rw [hcl]
      exact (hfound hcl).symm.trans h
  rw [Transduction.emitAt, List.filterMap_congr fun c _ ↦ hcopy c]
  refine filterMap_finRange_getElem? (List.le_sum_of_mem ?_)
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨_, hwin, w[p], hw _ (List.getElem_mem hp), rfl⟩

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

variable [DecidableEq α]

/-! ### Relabelling transductions -/

/-- The one-copy relabelling transduction of the quantifier-free docking process with guard `φ`
over the symbols `alphabet`: for each symbol, a clause docking it under the guard, then a
faithful clause. -/
def relabel (φ : WindowFormula α) (dock : α → α) (alphabet : List α) : Transduction α α where
  copies := 1
  clauses _ :=
    (alphabet.map fun a ↦ (φ.conj (.label a .var), dock a)) ++
      alphabet.map fun a ↦ (.label a .var, a)

private theorem flatMap_range_toList_eq_mapIdx {γ δ : Type*} (f : ℕ → γ → δ) :
    ∀ w : List γ, (List.range w.length).flatMap (fun n ↦ (w[n]?.map (f n)).toList) = w.mapIdx f
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.mapIdx_cons, ← flatMap_range_toList_eq_mapIdx (fun i ↦ f (i + 1)) l]
    simp

/-- On a word over the alphabet, the relabelling transduction computes the docking map. -/
theorem apply_relabel {φ : WindowFormula α} {dock : α → α} {alphabet : List α} {w : List α}
    (hw : ∀ a ∈ w, a ∈ alphabet) :
    (relabel φ dock alphabet).apply w = (Docking.ofQF φ dock).map w := by
  have hemit (n : ℕ) : (relabel φ dock alphabet).emitAt w n =
      (w[n]?.map fun a ↦ if n < w.length ∧ φ.Realize w n then dock a else a).toList := by
    by_cases hn : n < w.length
    · have hfind : alphabet.find? (fun b ↦ decide (w[n] = b)) = some w[n] := by
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 <| (List.find?_isSome
          (p := fun b ↦ decide (w[n] = b))).2 ⟨w[n], hw _ (List.getElem_mem hn), by simp⟩
        obtain rfl : w[n] = b := by simpa using List.find?_some hb
        exact hb
      have hnone : alphabet.find? (fun _ ↦ false) = none := List.find?_eq_none.2 (by simp)
      by_cases hφ : φ.Realize w n <;>
        simp [emitAt, relabel, List.finRange_succ, List.find?_append, List.find?_map, hφ, hn,
          hfind, hnone]
    · simp [emitAt, relabel, List.finRange_succ, List.find?_append, List.find?_map,
        List.getElem?_eq_none (Nat.le_of_not_lt hn)]
  rw [apply, funext hemit, flatMap_range_toList_eq_mapIdx]
  rfl

end Transduction

/-! ### Worked examples: feature change, deletion, epenthesis, and a left-local rule -/

section Example

private inductive Sym | a | b | c
  deriving DecidableEq

private def x : Walk := .var

/-- The position is flanked by `a`s. -/
private def flankedA : WindowFormula Sym := .conj (.label .a x.pred) (.label .a x.succ)

/-- This relabelling rewrites `b` as `c` between `a`s. The `b → c` clause precedes the faithful
`b → b` clause, so it wins in that context. -/
private def relabelBC : Transduction Sym Sym where
  copies := 1
  clauses _ := [(flankedA.conj (.label .b x), .c), (.label .b x, .b), (.label .a x, .a),
    (.label .c x, .c)]

example : relabelBC.apply [Sym.a, .b, .a] = [Sym.a, .c, .a] := by decide

/-- This deletion drops `b` between `a`s: a `b` matches a clause only when it is not flanked. -/
private def deleteFlanked : Transduction Sym Sym where
  copies := 1
  clauses _ := [(.label .a x, .a), (.label .c x, .c),
    ((WindowFormula.label .b x).conj flankedA.neg, .b)]

example : deleteFlanked.apply [Sym.a, .b, .a] = [Sym.a, .a] := by decide

/-- This insertion adds `a` after a final non-`a` symbol: copy 0 is faithful, and copy 1 carries
`a` only after a final `b` or `c`. -/
private def insertA : Transduction Sym Sym where
  copies := 2
  clauses k :=
    if k = 0 then [(.label .a x, .a), (.label .b x, .b), (.label .c x, .c)]
    else [(.conj (.disj (.label .b x) (.label .c x)) (.final x), .a)]

example : insertA.apply [Sym.a, .b] = [Sym.a, .b, .a] := by decide

/-- Relabelling then inserting: on `abab` the first `b`, between `a`s, becomes `c`, the final
`b` does not, and the final non-`a` triggers insertion. -/
example : insertA.apply (relabelBC.apply [Sym.a, .b, .a, .b]) = [Sym.a, .c, .a, .b, .a] := by
  decide

/-- This relabelling rewrites `b` as `c` after an `a`. Its guards read one position back and none
forward, so it is left-local with radius 1. -/
private def afterA : Transduction Sym Sym where
  copies := 1
  clauses _ := [(.conj (.label .a x.pred) (.label .b x), .c), (.label .b x, .b),
    (.label .c x, .c), (.label .a x, .a)]

example : afterA.LeftLocal 1 := by decide

-- Its 2-ISL rule computes the same function, and so does the transduction of that rule.
example : (afterA.toISLRule 1).apply [Sym.a, .b, .a, .b] = [Sym.a, .c, .a, .c] := by decide
example : ((afterA.toISLRule 1).toTransduction [.a, .b, .c]).apply [Sym.a, .b, .a, .b] =
    [Sym.a, .c, .a, .c] := by
  decide

end Example

end Subregular
