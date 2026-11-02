/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Linglib.Core.Computability.ElgotMezei
public import Linglib.Data.Wordlist.McCollumEtAl2020
public import Linglib.Phonology.Subregular.Docking

/-!
# McCollum, Baković, Mai and Meinhardt (2020): Unbounded circumambient patterns

ATR harmony in Tutrugbu spreads `[+ATR]` from the root leftward onto every prefix vowel unless
the initial vowel is `[+high]`, in which case a `[−high]` prefix vowel blocks it. McCollum,
Baković, Mai and Meinhardt show that this segmental pattern is unbounded circumambient in
Jardine's sense, their (13), like the tonal patterns Jardine took to be special: the surface
value of a medial `[−high]` vowel depends at once on the root to its right and on the initial
vowel to its left, however far away both are. No subsequential transducer computes the map in
either direction, (27), but a right-to-left pass that leaves some vowels undecided followed by
a left-to-right pass that decides them does, (28) and (29), so by Elgot and Mezei's
composition theorem the map is regular.

## Main definitions

* `Seg`: a prefix vowel with its height and ATR value, or a root with its ATR value
* `Harmonizes`: the paper's generalization, the context in which a prefix vowel harmonizes
* `tutrugbu`: the harmony as a docking process
* `markRight`, `resolveLeft`: the two passes of the mark-up analysis

## Implementation notes

* A word is its prefix vowels and its root, the consonants dropped as in the transducers of the
  paper's supplementary materials. Prefixes are underlyingly `[−ATR]` (§2.3.1), and docking
  raises a prefix vowel to `[+ATR]`.
* The words of `Data/Wordlist/McCollumEtAl2020.json` are transcribed from the page images, with
  the source's misprints recorded in their comments. The vowel of the negation prefix, printed
  much like ⟨í⟩, is a distinct glyph in the PDF and is read as ⟨ɪ́⟩, as the column headers of
  (3) and (5) and the tape (26) require.
* Not modelled: the conditionally transparent variant of §2.2, the suffixes and enclitics of
  (10), and phrasal harmony (11).
* The paper's conclusion that the map is not weakly deterministic uses Heinz and Lai's
  definition (17) informally, and its fn. 10 records that the definition admits mark-up-free
  loopholes, so the conclusion is not stated here.

## References

* [mccollum-bakovic-mai-meinhardt-2020]
* [jardine-2016a]
* [heinz-lai-2013]
* [elgot-mezei-1965]
-/

@[expose] public section

namespace McCollumEtAl2020

open Subregular

/-! ### The harmony -/

/-- A segment of a Tutrugbu word as harmony reads it is a prefix vowel with its height and ATR
value, or a root with its ATR value. -/
inductive Seg
  | pfx (high atr : Bool)
  | root (atr : Bool)
  deriving DecidableEq, Repr

/-- `s.raise` is `s` with `[+ATR]`, if `s` is a prefix vowel. -/
def Seg.raise : Seg → Seg
  | .pfx h _ => .pfx h true
  | .root a => .root a

/-- `s.isHigh` is the height of a prefix vowel; a root counts as not `[+high]`. -/
def Seg.isHigh : Seg → Bool
  | .pfx h _ => h
  | .root _ => false

/-- The initial vowel of `w` is `[+high]`. -/
def InitialHigh (w : List Seg) : Prop := ∃ a, w.head? = some (.pfx true a)

instance : DecidablePred InitialHigh := fun w ↦ by unfold InitialHigh; infer_instance

/-- Prefix vowel `i` of `w` harmonizes when a `[+ATR]` root follows it, unless the initial vowel
is `[+high]` and a `[−high]` vowel lies at or after `i`. -/
def Harmonizes (w : List Seg) (i : ℕ) : Prop :=
  .root true ∈ w.drop (i + 1) ∧ (InitialHigh w → ∀ a, .pfx false a ∉ w.drop i)

instance (w : List Seg) (i : ℕ) : Decidable (Harmonizes w i) := by
  unfold Harmonizes; infer_instance

/-- Tutrugbu ATR harmony docks `[+ATR]` on the prefix vowels that harmonize. -/
def tutrugbu : Docking Seg where
  dock := Seg.raise
  Docks := Harmonizes
  lt_length {w i} h := by
    by_contra hi
    have h1 := h.1
    rw [List.drop_eq_nil_of_le (by omega)] at h1
    exact List.not_mem_nil h1
  decDocks _ _ := inferInstance

/-! ### The data

The words of (1) to (8) and (27) are read off their transcriptions: the morphemes of the
underlying form give one segment per prefix vowel and one for the root, and the surface vowels
are aligned with them. -/

/-- The height and ATR value of the vowel letter `c`, after the inventory of §2.1, in which `ɪ`
and `ʊ` are the `[+high, −ATR]` vowels; any other character is no vowel. -/
def vowelFeatures : Char → Option (Bool × Bool)
  | 'i' | 'í' | 'ī' | 'u' | 'ú' | 'ū' => some (true, true)
  | 'ɪ' | 'ʊ' => some (true, false)
  | 'e' | 'é' | 'ē' | 'o' | 'ó' | 'ō' => some (false, true)
  | 'a' | 'á' | 'ā' | 'ɔ' | 'ɛ' => some (false, false)
  | _ => none

/-- `ofAnalysis a` is the underlying and the surface string of the word `a` analyses. The vowels
of its underlying form after the last morpheme boundary are the root's, and its surface vowels
are aligned with them. -/
def ofAnalysis (a : Wordlist.Analysis) : Option (List Seg × List Seg) := do
  let f := a.form
  let u := a.underlying.toList.reverse
  let pre := (u.dropWhile (· != '-')).reverse.filterMap vowelFeatures
  let rt ← ((u.takeWhile (· != '-')).filterMap vowelFeatures).getLast?
  let sv := f.segments.filterMap fun s ↦ s.toList.head?.bind vowelFeatures
  let rt' ← (sv.drop pre.length).head?
  let word (vs : List (Bool × Bool)) (r : Bool × Bool) : List Seg :=
    vs.map (fun v ↦ .pfx v.1 v.2) ++ [.root r.2]
  some (word pre rt, word (sv.take pre.length) rt')

/-- The map takes the underlying form of every word of (1) to (8) and (27) to its surface
form. -/
theorem tutrugbu_map_forms :
    ∀ a ∈ Wordlist.analyses, ∃ p ∈ ofAnalysis a, tutrugbu.map p.1 = p.2 := by
  decide

/-! ### Unbounded circumambience

The witness is a run of `[−high]` vowels between the initial vowel and the root. With a
`[−high]` initial and a `[+ATR]` root the whole run harmonizes, as in (8h); a `[+high]` initial
blocks it, as in (8g); a `[−ATR]` root triggers nothing, as in (5a) against (5d). -/

private theorem harmonizes_flankWord_mid (x y : Seg) (d : ℕ) :
    Harmonizes (flankWord x (.pfx false false) y (2 * d + 1)) (d + 1) ↔
      y = .root true ∧ ∀ a, x ≠ .pfx true a := by
  rw [Harmonizes, mem_drop_flankWord_iff (by simp) (by omega), drop_flankWord (by omega)]
  simp [InitialHigh, show 2 * d + 1 - d = d + 1 by omega, List.replicate_succ, eq_comm]

/-- Tutrugbu ATR harmony is unbounded circumambient in the sense of (13). At every distance a medial
`[−high]` vowel harmonizes, and changing either the initial vowel or the root alone undoes it. -/
theorem tutrugbu_isUnboundedCircumambient : IsUnboundedCircumambient tutrugbu.map :=
  tutrugbu.isUnboundedCircumambient_of_flanks (fill := .pfx false false) (xOn := .pfx false false)
    (yOn := .root true) (xOff := .pfx true false) (yOff := .root false)
    (n := fun d ↦ 2 * d + 1) (t := fun d ↦ d + 1) (by decide) (fun _ ↦ by omega)
    (fun _ ↦ by omega) (fun d ↦ (harmonizes_flankWord_mid _ _ d).mpr ⟨rfl, by simp⟩)
    (fun d h ↦ ((harmonizes_flankWord_mid _ _ d).mp h).2 false rfl)
    (fun d h ↦ by simpa using ((harmonizes_flankWord_mid _ _ d).mp h).1)

theorem tutrugbu_twoSidedUnboundedDependence : TwoSidedUnboundedDependence tutrugbu.map :=
  tutrugbu_isUnboundedCircumambient.twoSidedUnboundedDependence

/-- No subsequential transducer computes Tutrugbu ATR harmony, in either direction, (27). -/
theorem tutrugbu_not_isSubsequential : ∀ d, ¬ IsSubsequential d tutrugbu.map :=
  tutrugbu_twoSidedUnboundedDependence.not_isSubsequential fun _ ↦ tutrugbu.map_length

/-! ### The mark-up analysis

The right-to-left pass (28), Fig. 8 of the supplementary materials, decides each prefix vowel
it can: before a `[−ATR]` root a vowel stays `[−ATR]`, and a `[+high]` vowel before a `[+ATR]`
root with no `[−high]` vowel in between is `[+ATR]`. From the first `[−high]` vowel leftward it
leaves the value open, writing Ê for a `[+high]` vowel and Ψ for a `[−high]` one. The
left-to-right pass (29), Fig. 9, reads the height of the initial vowel: if it is `[+high]` the
blocking conditions hold and every open vowel stays `[−ATR]`, and otherwise every open vowel is
`[+ATR]`. -/

/-- A symbol of the intermediate alphabet is a decided segment, or a prefix vowel of known
height whose ATR value is left open, Ê when `[+high]` and Ψ when `[−high]`. -/
inductive Mark
  | seg (s : Seg)
  | undecided (high : Bool)
  deriving DecidableEq, Repr

/-- `m.isHigh` is the height of a marked segment. -/
def Mark.isHigh : Mark → Bool
  | .seg s => s.isHigh
  | .undecided h => h

/-- The right-to-left pass (28). Its state records whether a `[+ATR]` root has been read and
whether a `[−high]` vowel has. -/
def markRight : Mealy (Bool × Bool) Seg Mark where
  start := (false, false)
  step p s := match s with
    | .root true => (true, p.2)
    | .pfx false _ => (p.1, true)
    | _ => p
  output p s := match s with
    | .pfx h false => if !p.1 then .seg s else if h && !p.2 then .seg (.pfx h true)
      else .undecided h
    | s => .seg s

/-- The left-to-right pass (29). Its state records the height of the initial vowel. -/
def resolveLeft : Mealy (Option Bool) Mark Seg where
  start := none
  step b m := some (b.getD m.isHigh)
  output b m := match m with
    | .seg s => s
    | .undecided h => .pfx h !(b.getD h)

private theorem markRight_evalFrom (p : Bool × Bool) (xs : List Seg) :
    markRight.evalFrom p xs =
      (p.1 || decide (.root true ∈ xs), p.2 || decide (∃ a, .pfx false a ∈ xs)) := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih =>
    rw [Mealy.evalFrom_cons, ih]
    rcases x with ⟨_ | _, _⟩ | _ | _ <;> simp [markRight]

private theorem resolveLeft_eval (xs : List Mark) :
    resolveLeft.eval xs = xs.head?.map Mark.isHigh := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp only [Mealy.eval, Mealy.evalFrom_cons, List.head?_cons, Option.map_some]
    induction xs generalizing x with
    | nil => rfl
    | cons y ys ih => simpa [resolveLeft] using ih x

private theorem isHigh_markRight_output (p : Bool × Bool) (s : Seg) :
    (markRight.output p s).isHigh = s.isHigh := by
  rcases s with ⟨h, _ | _⟩ | a <;> simp only [markRight] <;> (try split_ifs) <;> rfl

private theorem head?_take_markRight_runRight (w : List Seg) (i : ℕ) :
    ((markRight.runRight w).take i).head?.map Mark.isHigh = (w.take i).head?.map Seg.isHigh := by
  rcases i with _ | i
  · rfl
  rw [List.head?_take, List.head?_take, ite_eq_right i.add_one_ne_zero,
    ite_eq_right i.add_one_ne_zero,
    List.head?_eq_getElem?, List.head?_eq_getElem?, Mealy.getElem?_runRight, Option.map_map]
  exact Option.map_congr fun s _ ↦ isHigh_markRight_output _ s

/-- The mark-up analysis computes Tutrugbu ATR harmony, marking right to left and then
resolving left to right. -/
theorem tutrugbu_map_eq_resolve_mark (w : List Seg) :
    tutrugbu.map w = resolveLeft.run (markRight.runRight w) := by
  refine List.ext_getElem? fun i ↦ ?_
  rw [Docking.map_getElem?, Mealy.getElem?_run, Mealy.getElem?_runRight,
    resolveLeft_eval, head?_take_markRight_runRight, Mealy.eval,
    show markRight.start = (false, false) from rfl, markRight_evalFrom]
  rcases ha : w[i]? with _ | a
  · rfl
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  have hstate : (w.take i).head?.map Seg.isHigh =
      if i = 0 then none else some (w.head?.any Seg.isHigh) := by
    rcases i with _ | i
    · rfl
    · simp [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < w.length by omega)]
  have hinit : InitialHigh w ↔ w.head?.any Seg.isHigh := by
    unfold InitialHigh
    rcases w.head? with _ | (⟨_ | _, _⟩ | _) <;> simp [Seg.isHigh]
  have h0 : i = 0 → w.head?.any Seg.isHigh = w[i].isHigh := by
    rintro rfl
    simp [List.head?_eq_getElem?, List.getElem?_eq_getElem hi]
  simp only [Option.map_some, Option.some_inj, Bool.false_or, List.mem_reverse, hstate,
    tutrugbu, Harmonizes, hinit, List.drop_eq_getElem_cons hi, List.mem_cons, not_or]
  revert h0
  generalize w.head?.any Seg.isHigh = IH
  by_cases hT : Seg.root true ∈ w.drop (i + 1) <;>
    by_cases hB : ∃ a, Seg.pfx false a ∈ w.drop (i + 1) <;>
    rcases w[i] with ⟨_ | _, _ | _⟩ | _ <;> cases IH <;> by_cases i = 0 <;>
    simp_all [resolveLeft, markRight, Seg.raise, Seg.isHigh] <;> tauto

/-- Tutrugbu ATR harmony is regular. The mark-up analysis is a left-to-right Mealy pass after a
right-to-left one, and a bimachine computes such a composite. -/
theorem tutrugbu_isBimachineComputable : IsBimachineComputable tutrugbu.map := by
  rw [show tutrugbu.map = resolveLeft.run ∘ markRight.runRight from
    funext tutrugbu_map_eq_resolve_mark]
  exact resolveLeft.isBimachineComputable_run_comp_runRight markRight

end McCollumEtAl2020
