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
formula at a position is a `Subregular.WindowFormula`, reading a bounded window through
successor and predecessor steps. [chandlee-jardine-2019] report that the quantifier-free string
transductions are exactly the input strictly local functions. This file proves the one-sided
case: over a finite alphabet, the transductions whose guards read only backward compute exactly
the left input strictly local functions.

The transductions here are **order-preserving** in the sense of [dolatian-2020] (§7.4.2): the
output is read off in the order (input position, copy), so the output successor is induced
rather than defined by formulas of its own. Transductions that define it, such as
[dolatian-2020]'s iconic reduplication, are not represented.

## Main definitions

* `Subregular.Transduction`: a decision list of guarded clauses, each emitting a block.
* `Transduction.apply`: the output string, computably.
* `Transduction.LeftLocal r`: every guard reads at most `r` positions back and none forward.
* `ISLRule.toTransduction`: the left-local transduction with a clause for each window and
  symbol, guarded by `WindowFormula.window`.
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
  clauses : List (WindowFormula α × List β)

namespace Transduction

variable (T : Transduction α β)

/-- A transduction is **left-local** with radius `r` if every guard is backward-bounded by `r`,
reading only its position and the `r` positions before it. -/
def LeftLocal (r : ℕ) : Prop :=
  ∀ cl ∈ T.clauses, cl.1.BackBounded r

variable [DecidableEq α]

/-- The block emitted at input position `n`: that of the first clause whose guard holds there,
or nothing. -/
def emitAt (w : List α) (n : ℕ) : List β :=
  ((T.clauses.find? fun cl ↦ cl.1.Realize w n).map Prod.snd).getD []

/-- The output string: the blocks emitted at the input positions, left to right. -/
def apply (w : List α) : List β :=
  (List.range w.length).flatMap (T.emitAt w)

@[simp] theorem apply_nil : T.apply [] = [] := rfl

variable {T} {w : List α} {n : ℕ}

theorem emitAt_eq_of_mem {cl : WindowFormula α × List β} (hcl : cl ∈ T.clauses)
    (h : cl.1.Realize w n) (huniq : ∀ cl' ∈ T.clauses, cl'.1.Realize w n → cl'.2 = cl.2) :
    T.emitAt w n = cl.2 := by
  obtain ⟨cl', hcl'⟩ := Option.isSome_iff_exists.1 <|
    (List.find?_isSome (p := fun cl : WindowFormula α × List β ↦ decide (cl.1.Realize w n))).2
      ⟨cl, hcl, decide_eq_true h⟩
  rw [emitAt, hcl', Option.map_some, Option.getD_some,
    huniq _ (List.mem_of_find?_eq_some hcl') (by simpa using List.find?_some hcl')]

/-! ### Left-local transductions are input strictly local -/

namespace LeftLocal

variable {r : ℕ} (hT : T.LeftLocal r)
include hT

theorem emitAt_congr {w w' : List α} {n n' : ℕ} (hn : n < w.length) (hn' : n' < w'.length)
    (hlbl : ∀ j ≤ r, w[n - j]? = w'[n' - j]?) (hedge : ∀ j ≤ r, (j ≤ n ↔ j ≤ n')) :
    T.emitAt w n = T.emitAt w' n' :=
  congrArg (fun o ↦ (o.map Prod.snd).getD []) <| List.find?_congr fun cl hcl ↦
    decide_eq_decide.2 <| WindowFormula.BackBounded.realize_congr hn hn' hlbl hedge (hT cl hcl)

theorem emitAt_append {u : List α} (v : List α) {p : ℕ} (hp : p < u.length) :
    T.emitAt (u ++ v) p = T.emitAt u p :=
  hT.emitAt_congr (by simp; omega) hp (fun _ _ ↦ List.getElem?_append_left (by omega))
    fun _ _ ↦ Iff.rfl

theorem emitAt_eq_emitAt_rtake {w : List α} {p : ℕ} (hp : p < w.length) :
    T.emitAt w p = T.emitAt ((w.take (p + 1)).rtake (r + 1)) (min r p) := by
  have hlen : (w.take (p + 1)).length = p + 1 := by simp; omega
  refine hT.emitAt_congr hp (by simp [hlen]) (fun j hj ↦ ?_) fun _ _ ↦ by omega
  rw [List.getElem?_rtake, hlen, List.getElem?_take, ite_eq_left (by omega)]
  congr 1
  omega

theorem apply_append_singleton (u : List α) (x : α) :
    T.apply (u ++ [x]) = T.apply u ++ T.emitAt (u ++ [x]) u.length := by
  rw [apply, List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
    List.flatMap_singleton, apply, List.flatMap_congr fun p hp ↦
      hT.emitAt_append [x] (List.mem_range.1 hp)]

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
    ((WindowFormula.label a .var).conj (.window r u), ρ.windowOutput u a)⟩

theorem leftLocal_toTransduction : (ρ.toTransduction alphabet).LeftLocal r := by
  intro cl hcl
  simp only [toTransduction, List.mem_flatMap, List.mem_map] at hcl
  obtain ⟨u, hu, a, -, rfl⟩ := hcl
  exact ⟨⟨Nat.zero_le r, le_rfl⟩, WindowFormula.window_backBounded (mem_windows.1 hu).1⟩

variable [DecidableEq α]

theorem emitAt_toTransduction {w : List α} (hw : ∀ a ∈ w, a ∈ alphabet) {p : ℕ}
    (hp : p < w.length) :
    (ρ.toTransduction alphabet).emitAt w p = ρ.windowOutput ((w.take p).rtake r) w[p] := by
  have hguard {u : List α} (hu : u ∈ windows alphabet r) (a : α) :
      ((WindowFormula.label a .var).conj (.window r u)).Realize w p ↔
        w[p] = a ∧ (w.take p).rtake r = u := by
    rw [WindowFormula.realize_conj, WindowFormula.realize_label_var,
      WindowFormula.realize_window hp (mem_windows.1 hu).1, List.getElem?_eq_getElem hp,
      Option.some.injEq]
  have hwin : (w.take p).rtake r ∈ windows alphabet r :=
    mem_windows.2 ⟨List.length_rtake_le r _, fun a ha ↦
      hw a (List.mem_of_mem_take ((List.rtake_suffix r _).subset ha))⟩
  have hmem {cl} : cl ∈ (ρ.toTransduction alphabet).clauses ↔ ∃ u ∈ windows alphabet r,
      ∃ a ∈ alphabet, ((WindowFormula.label a .var).conj (.window r u), ρ.windowOutput u a) = cl :=
    by simp [toTransduction]
  refine Transduction.emitAt_eq_of_mem (hmem.2 ⟨_, hwin, w[p], hw _ (List.getElem_mem hp), rfl⟩)
    ((hguard hwin _).2 ⟨rfl, rfl⟩) fun cl hcl h ↦ ?_
  obtain ⟨u, hu, a, -, rfl⟩ := hmem.1 hcl
  obtain ⟨rfl, rfl⟩ := (hguard hu a).1 h
  rfl

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
def relabel (φ : WindowFormula α) (dock : α → α) (alphabet : List α) : Transduction α α :=
  ⟨alphabet.flatMap fun a ↦
    [(φ.conj (.label a .var), [dock a]), (φ.neg.conj (.label a .var), [a])]⟩

variable [DecidableEq α]

private theorem flatMap_range_toList_eq_mapIdx {γ δ : Type*} (f : ℕ → γ → δ) :
    ∀ w : List γ, (List.range w.length).flatMap (fun n ↦ (w[n]?.map (f n)).toList) = w.mapIdx f
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.mapIdx_cons, ← flatMap_range_toList_eq_mapIdx (fun i ↦ f (i + 1)) l]
    simp

theorem apply_relabel {φ : WindowFormula α} {dock : α → α} {alphabet : List α} {w : List α}
    (hw : ∀ a ∈ w, a ∈ alphabet) :
    (relabel φ dock alphabet).apply w = (Docking.ofQF φ dock).map w := by
  have hmem {cl} : cl ∈ (relabel φ dock alphabet).clauses ↔ ∃ a ∈ alphabet,
      cl = (φ.conj (.label a .var), [dock a]) ∨ cl = (φ.neg.conj (.label a .var), [a]) := by
    simp [relabel]
  have hemit {n : ℕ} (hn : n < w.length) : (relabel φ dock alphabet).emitAt w n =
      (w[n]?.map fun a ↦ if n < w.length ∧ φ.Realize w n then dock a else a).toList := by
    simp only [List.getElem?_eq_getElem hn, Option.map_some, Option.toList_some, hn, true_and]
    refine emitAt_eq_of_mem (cl := ((if φ.Realize w n then φ else φ.neg).conj (.label w[n] .var),
      [if φ.Realize w n then dock w[n] else w[n]])) (hmem.2 ⟨_, hw _ (List.getElem_mem hn), ?_⟩)
      (by split_ifs <;> simp [*]) fun cl hcl h ↦ ?_
    · split_ifs <;> simp
    · obtain ⟨a, -, rfl | rfl⟩ := hmem.1 hcl <;> simp_all
  rw [apply, List.flatMap_congr fun n hn ↦ hemit (List.mem_range.1 hn),
    flatMap_range_toList_eq_mapIdx]
  rfl

end Transduction

/-! ### Worked examples: feature change, deletion, epenthesis, and a left-local rule -/

section Example

private inductive Sym | a | b | c
  deriving DecidableEq

private def x : Walk := .var

/-- The position is flanked by `a`s. -/
private def flankedA : WindowFormula Sym := .conj (.label .a x.pred) (.label .a x.succ)

/-- The faithful clauses of the demo alphabet. -/
private def faithful : List (WindowFormula Sym × List Sym) :=
  [(.label .a x, [.a]), (.label .b x, [.b]), (.label .c x, [.c])]

/-- This relabelling rewrites `b` as `c` between `a`s. The `b → c` clause precedes the faithful
clauses, so it wins in that context. -/
private def relabelBC : Transduction Sym Sym := ⟨(flankedA.conj (.label .b x), [.c]) :: faithful⟩

example : relabelBC.apply [Sym.a, .b, .a] = [Sym.a, .c, .a] := by decide

/-- This deletion drops `b` between `a`s: there its clause emits nothing. -/
private def deleteFlanked : Transduction Sym Sym := ⟨(flankedA.conj (.label .b x), []) :: faithful⟩

example : deleteFlanked.apply [Sym.a, .b, .a] = [Sym.a, .a] := by decide

/-- This insertion adds `a` after a final non-`a` symbol: there the clause emits the symbol and
then `a`. -/
private def insertA : Transduction Sym Sym :=
  ⟨[((WindowFormula.label .b x).conj (.final x), [.b, .a]),
    ((WindowFormula.label .c x).conj (.final x), [.c, .a])] ++ faithful⟩

example : insertA.apply [Sym.a, .b] = [Sym.a, .b, .a] := by decide

/-- Relabelling then inserting: on `abab` the first `b`, between `a`s, becomes `c`, the final
`b` does not, and the final non-`a` triggers insertion. -/
example : insertA.apply (relabelBC.apply [Sym.a, .b, .a, .b]) = [Sym.a, .c, .a, .b, .a] := by
  decide

/-- The 2-ISL rule rewriting `b` as `c` after an `a`. -/
private def afterA : ISLRule 2 Sym Sym :=
  ⟨fun window s ↦ if window = [.a] ∧ s = .b then [.c] else [s]⟩

-- Its transduction computes it.
example : (afterA.toTransduction [.a, .b, .c]).apply [Sym.a, .b, .a, .b] = [Sym.a, .c, .a, .c] := by
  decide

end Example

end Subregular
