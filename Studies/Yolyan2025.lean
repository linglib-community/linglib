module

public import Linglib.Phonology.Subregular.Dependence
public import Linglib.Phonology.Subregular.BMRS
public import Linglib.Phonology.Tone.Surfacing
public import Linglib.Data.Wordlist.Yolyan2025
public import Studies.McCollumEtAl2020

/-!
# Yolyan (2025): A Logical Characterization of Weak Determinism as Simultaneous Application

This file formalizes Yolyan's definition of the weakly deterministic string functions
as the simultaneous application `P^L ⊙ P^R` of a backward and a forward Boolean monadic
recursive scheme (Def. 5.1), in the BMRS formalism of Bhaskar, Jardine, Chandlee and Oakden
(`Subregular.BMRS`), whose one-sided fragments characterize the left- and right-subsequential
functions. The operator ⊙ (Def. 4.1) acts per position on the input value and the two
programs' output values, so that a change survives iff either program makes it (Prop. 4.2);
`SimulModels` lifts it to programs (Def. 4.3) for the length-preserving maps of §5, and
`IsBmrsWeaklyDeterministic` is Def. 5.1.

The negative results of §5.3 share one argument. On a far-left and on a far-right
perturbation of a witness word the target is unchanged, so ⊙ is conjunction there and both
one-sided outputs are forced true; each transports to the base word by one-sided locality, and
recombining forces the base target unchanged.
`not_isBmrsWeaklyDeterministic_of_requiresBothSides` proves this once from the substrate's
`RequiresBothSides` witness, and Sour Grapes harmony (Thm. 5.2, the conjecture of
Heinz and Lai), Copperbelt Bemba high-tone spreading (Prop. 5.4) and Tutrugbu ATR harmony
(Prop. 5.5, through `McCollumEtAl2020`) are its instances. On the positive side, with no
underlying stress the input predicate is constantly false and ⊙ collapses to disjunction,
(5.15), which recovers Koser and Jardine's program for leftmost-heavy-otherwise-leftmost
stress in Lushootseed as the simultaneous application of its two one-sided halves (§5.2). The
conjunctive dual ⊘ of §6.3 (Def. 6.5) expresses Sour Grapes exactly (`sourGrapes_conjunctive`).

## Implementation notes

* ⊙ and ⊘ are stated on values (`combine`, `combineC`), where the algebra of Prop. 4.4 is a
  finite computation; the program-level operators lift them pointwise. Copy sets are omitted,
  as none of the §5 maps needs them.
* The head types of the two programs are unconstrained, which only strengthens the negative
  results. The exclusion uses the `d = 0` instance of the witness, since one-sidedness is global
  rather than window-bounded.
* Bemba spreading is a `Tone.Surfacing` instance built from the paper's characterization: a
  high spreads to the word end when no high follows it, and onto the next two tone-bearing
  units when one does. Unlike plateauing, the surface set is not convex and the map is neither
  monotone nor idempotent. The words of Example 2.11 are in `Data/Wordlist/Yolyan2025.json`, their
  tones read off the accents; the Tutrugbu words of Example 2.12 are McCollum et al.'s, and
  `Data/Wordlist/McCollumEtAl2020.json` cites them.
* Thm. 5.2 settles Heinz and Lai's conjecture under Def. 5.1; under their own definition Lamont,
  O'Hara and Smith express Sour Grapes as a composition of contradirectional subsequential
  functions.

## TODO

* Thm. 5.3 (Yidiny liquid dissimilation) awaits a map for that pattern.

## References

* [yolyan-2025]
* [bhaskar-jardine-chandlee-oakden-2020]
* [heinz-lai-2013]
* [koser-jardine-2020]
* [mccollum-bakovic-mai-meinhardt-2020]
* [jardine-2016a]
* [padgett-1995]
* [wilson-2003]
* [lamont-ohara-smith-2019]
-/

@[expose] public section

namespace Yolyan2025

open Subregular Subregular.BMRS

/-- `x` is the single BMRS index variable. -/
abbrev x : Walk := .var

variable {α : Type*} [DecidableEq α]

/-! ### Simultaneous application, at the value level

Def. 4.1 (⊙) and Def. 6.5 (⊘) act per input position on the input value and the two
programs' output values; the program-level operators lift these pointwise. -/

/-- Simultaneous application ⊙ on values (Def. 4.1) keeps a change iff either program makes
it. -/
def combine (pin a b : Bool) : Bool := if pin then a && b else a || b

/-- Conjunctive simultaneous application ⊘ on values (Def. 6.5) keeps a change iff both
programs make it. -/
def combineC (pin a b : Bool) : Bool := if pin then a || b else a && b

@[simp] theorem combine_true (a b : Bool) : combine true a b = (a && b) := rfl

-- (5.15)
@[simp] theorem combine_false (a b : Bool) : combine false a b = (a || b) := rfl

@[simp] theorem combineC_true (a b : Bool) : combineC true a b = (a || b) := rfl

@[simp] theorem combineC_false (a b : Bool) : combineC false a b = (a && b) := rfl

-- Prop. 4.2
theorem combine_ne_iff (pin a b : Bool) :
    combine pin a b ≠ pin ↔ a ≠ pin ∨ b ≠ pin := by decide +revert

-- Prop. 4.4, (i)
theorem combine_comm (pin a b : Bool) : combine pin a b = combine pin b a := by
  decide +revert

-- Prop. 4.4, (ii)
theorem combine_assoc (pin a b c : Bool) :
    combine pin (combine pin a b) c = combine pin a (combine pin b c) := by decide +revert

-- Prop. 4.4, (iii)
theorem combine_id (pin a : Bool) : combine pin a pin = a := by decide +revert

theorem combineC_eq_not_combine (pin a b : Bool) :
    combineC pin a b = !combine pin (!a) (!b) := by decide +revert

theorem combineC_comm (pin a b : Bool) : combineC pin a b = combineC pin b a := by
  decide +revert

theorem combineC_assoc (pin a b c : Bool) :
    combineC pin (combineC pin a b) c = combineC pin a (combineC pin b c) := by
  decide +revert

/-! ### Weak determinism as simultaneous application (Defs. 4.1, 4.3, 5.1) -/

/-- `b` is the value of the ⊙-combined output predicate for `σ` at `i` (Def. 4.1), the two
programs' output values combined against the input value. -/
def SimulEval {L R : Type} (PL : Program α L) (PR : Program α R) (hL : L) (hR : R)
    (w : List α) (i : ℕ) (σ : α) (b : Bool) : Prop :=
  ∃ bL bR, Eval PL w i (.call hL x) bL ∧ Eval PR w i (.call hR x) bR ∧
    b = combine (decide (w[i]? = some σ)) bL bR

/-- The simultaneous application `P^L ⊙ P^R` models `f` (Def. 4.3, for the length-preserving
maps of §5) when each output symbol is the one whose ⊙-combined output predicate holds. -/
def SimulModels {L R : Type} (PL : Program α L) (PR : Program α R)
    (outL : α → L) (outR : α → R) (f : List α → List α) : Prop :=
  ∀ w : List α, (f w).length = w.length ∧
    ∀ i < w.length, ∀ σ : α,
      ((f w)[i]? = some σ ↔ SimulEval PL PR (outL σ) (outR σ) w i σ true)

/-- `f` is weakly deterministic (Def. 5.1) when it is the simultaneous application of a
backward (`BMRSᵖ`) and a forward (`BMRSˢ`) program. -/
def IsBmrsWeaklyDeterministic (f : List α → List α) : Prop :=
  ∃ (L R : Type) (PL : Program α L) (PR : Program α R) (outL : α → L) (outR : α → R),
    PL.Backward ∧ PR.Forward ∧ SimulModels PL PR outL outR f

/-! ### The exclusion argument of §5.3 -/

/-- A map that requires both sides is not weakly deterministic, with Thm. 5.2 and Props. 5.4 and 5.5
as instances. -/
theorem not_isBmrsWeaklyDeterministic_of_requiresBothSides {f : List α → List α}
    (hf : RequiresBothSides f) : ¬ IsBmrsWeaklyDeterministic f := by
  rintro ⟨L, R, PL, PR, outL, outR, hPL, hPR, hm⟩
  obtain ⟨base, i, hi, hchange, hw⟩ := hf 0
  obtain ⟨uL, ⟨hLlen, hLag⟩, hLsym, hLrev⟩ := hw .left
  obtain ⟨uR, ⟨hRlen, hRag⟩, hRsym, hRrev⟩ := hw .right
  simp only [Edge.window_left, Nat.sub_zero] at hLag
  simp only [Edge.window_right, Nat.add_zero] at hRag
  set σ := base[i]'hi with hσ
  have hbase : base[i]? = some σ := List.getElem?_eq_getElem hi
  -- the far-left run: the target is unchanged, so both components are forced true
  have hLboth : Eval PL uL i (.call (outL σ) x) true ∧
      Eval PR uL i (.call (outR σ) x) true := by
    obtain ⟨bL, bR, hevL, hevR, hcomb⟩ :=
      ((hm uL).2 i (hLlen ▸ hi) σ).mp (hLrev.trans (hLsym.trans hbase))
    rw [decide_eq_true (hLsym.trans hbase), combine_true, eq_comm,
      Bool.and_eq_true] at hcomb
    exact ⟨hcomb.1 ▸ hevL, hcomb.2 ▸ hevR⟩
  -- the far-right run, symmetrically
  have hRboth : Eval PL uR i (.call (outL σ) x) true ∧
      Eval PR uR i (.call (outR σ) x) true := by
    obtain ⟨bL, bR, hevL, hevR, hcomb⟩ :=
      ((hm uR).2 i (hRlen ▸ hi) σ).mp (hRrev.trans (hRsym.trans hbase))
    rw [decide_eq_true (hRsym.trans hbase), combine_true, eq_comm,
      Bool.and_eq_true] at hcomb
    exact ⟨hcomb.1 ▸ hevL, hcomb.2 ▸ hevR⟩
  -- transport each one-sided output to the base word and recombine
  have hevL : Eval PL base i (.call (outL σ) x) true :=
    hRboth.1.congr_take hPL hRlen rfl hRag.symm
  have hevR : Eval PR base i (.call (outR σ) x) true :=
    hLboth.2.congr_drop hPR hLlen rfl hLag.symm
  exact hchange ((((hm base).2 i hi σ).mpr
    ⟨true, true, hevL, hevR, by rw [decide_eq_true hbase]; rfl⟩).trans hbase.symm)

/-! ### Sour Grapes harmony is not weakly deterministic (Thm. 5.2)

The pathology of [padgett-1995] and [wilson-2003], Example 2.10: `−` becomes `+` iff a `+`
lies anywhere to its left and no blocker `⊟` anywhere to its right, so spreading happens only
when it can reach the end of the word. -/

/-- The schematic Sour Grapes alphabet has a trigger `+`, a target `−` and a blocker `⊟`. -/
inductive SG
  | plus | minus | blk
  deriving DecidableEq, Repr

/-- In Sour Grapes harmony a `−` surfaces `+` iff a trigger precedes it and no blocker follows
it. -/
def sourGrapes (w : List SG) : List SG :=
  w.mapIdx fun i σ ↦
    if σ = .minus ∧ .plus ∈ w.take i ∧ .blk ∉ w.drop i then .plus else σ

private theorem sourGrapes_flankWord_mid {u v : SG} {d : ℕ} :
    (sourGrapes (flankWord u .minus v (2 * d + 1)))[d + 1]? =
      some (if u = .plus ∧ v ≠ .blk then .plus else .minus) := by
  rw [sourGrapes, List.getElem?_mapIdx, getElem?_flankWord_mid (by omega) (by omega),
    Option.map_some]
  by_cases h : u = .plus ∧ v ≠ .blk
  · rw [ite_eq_left h, ite_eq_left ⟨rfl,
      (mem_take_flankWord_iff (by decide) (by omega)).mpr h.1,
      fun hb ↦ h.2 ((mem_drop_flankWord_iff (by decide) (by omega)).mp hb)⟩]
  · rw [ite_eq_right h, ite_eq_right fun ⟨_, ht, hd⟩ ↦
      h ⟨(mem_take_flankWord_iff (by decide) (by omega)).mp ht,
        fun hv ↦ hd ((mem_drop_flankWord_iff (by decide) (by omega)).mpr hv)⟩]

-- Thm. 5.2
theorem sourGrapes_requiresBothSides : RequiresBothSides sourGrapes :=
  RequiresBothSides.of_flanks (fill := SG.minus) (xOn := SG.plus)
    (yOn := SG.minus) (xOff := SG.minus) (yOff := SG.blk) (n := fun d ↦ 2 * d + 1)
    (t := fun d ↦ d + 1) (fun d ↦ by omega) (fun d ↦ by omega)
    (fun d ↦ by rw [sourGrapes_flankWord_mid]; simp)
    (fun d ↦ by rw [sourGrapes_flankWord_mid]; simp)
    (fun d ↦ by rw [sourGrapes_flankWord_mid]; simp)

-- Thm. 5.2
theorem sourGrapes_not_bmrsWeaklyDeterministic :
    ¬ IsBmrsWeaklyDeterministic sourGrapes :=
  not_isBmrsWeaklyDeterministic_of_requiresBothSides sourGrapes_requiresBothSides

-- Example 2.12, Prop. 5.5
theorem tutrugbu_not_bmrsWeaklyDeterministic :
    ¬ IsBmrsWeaklyDeterministic McCollumEtAl2020.tutrugbu.map :=
  not_isBmrsWeaklyDeterministic_of_requiresBothSides
    McCollumEtAl2020.tutrugbu_requiresBothSides

/-! ### Bemba high-tone spreading is not weakly deterministic (Prop. 5.4)

Copperbelt Bemba, Example 2.11, after Jardine. A high tone spreads to the end of the word when no
high follows it, and only onto the next two tone-bearing units when one does. -/

/-- The Bemba tonal alphabet has a high and a low tone. -/
inductive BTone
  | H | L
  deriving DecidableEq, Repr

/-- Position `i` surfaces H when it is an underlying H, within the two-TBU bounded spread of a
preceding H, or at or after the last H (unbounded spread to the word end). -/
def bembaSurfaces (w : List BTone) (i : ℕ) : Prop :=
  i < w.length ∧ (w[i]? = some .H
    ∨ (∃ j < i, w[j]? = some .H ∧ i ≤ j + 2)
    ∨ ∃ j ≤ i, w[j]? = some .H ∧ ∀ k < w.length, w[k]? = some .H → k ≤ j)

instance (w : List BTone) (i : ℕ) : Decidable (bembaSurfaces w i) := by
  unfold bembaSurfaces
  infer_instance

/-- Bemba high-tone spreading is a surfacing process. -/
def bemba : Tone.Surfacing BTone where
  hi := .H
  lo := .L
  Surfaces := bembaSurfaces
  hi_ne_lo := by decide
  lt_length h := h.1
  surfaces_of_hi h := ⟨(List.getElem?_eq_some_iff.mp h).1, .inl h⟩
  decSurfaces _ _ := inferInstance

/-- `toneOf c` is the tone of the vowel letter `c`, high under an acute and low otherwise; any
other character is no vowel. -/
def toneOf : Char → Option BTone
  | 'á' | 'é' | 'í' | 'ó' | 'ú' => some .H
  | 'a' | 'e' | 'i' | 'o' | 'u' | 'à' | 'è' | 'ì' | 'ò' | 'ù' => some .L
  | _ => none

/-- `ofAnalysis a` is the tones of the underlying and of the surface form of the word `a`
analyses, one per vowel, when the two have as many vowels. -/
def ofAnalysis (a : Wordlist.Analysis) : Option (List BTone × List BTone) :=
  let u := a.underlying.toList.filterMap toneOf
  let s := a.form.form.toList.filterMap toneOf
  if u.length = s.length then some (u, s) else none

-- Example 2.11
theorem bemba_map_forms : ∀ a ∈ Wordlist.analyses, ∀ p ∈ ofAnalysis a, bemba.map p.1 = p.2 := by
  decide

/-- All words of Example 2.11 but the second of (b), whose surface lengthens a vowel, keep their
number of vowels. -/
example : (Wordlist.analyses.filterMap ofAnalysis).length = 4 := by decide

private theorem bembaSurfaces_flankWord_HL {d : ℕ} :
    bembaSurfaces (flankWord .H .L .L (2 * d + 4)) (d + 3) := by
  refine ⟨by rw [length_flankWord]; omega,
    .inr (.inr ⟨0, by omega, getElem?_flankWord_zero, fun k hk hkH ↦ ?_⟩)⟩
  rw [length_flankWord] at hk
  rw [getElem?_flankWord] at hkH
  split_ifs at hkH <;> first | omega | exact BTone.noConfusion (Option.some.inj hkH)

private theorem not_bembaSurfaces_flankWord_HH {d : ℕ} :
    ¬ bembaSurfaces (flankWord .H .L .H (2 * d + 4)) (d + 3) := by
  rintro ⟨-, h | ⟨j, hj, hjH, hspread⟩ | ⟨j, hj, hjH, hlast⟩⟩
  · rw [getElem?_flankWord] at h
    split_ifs at h <;> first | omega | exact BTone.noConfusion (Option.some.inj h)
  · rw [getElem?_flankWord] at hjH
    split_ifs at hjH <;> first | omega | exact BTone.noConfusion (Option.some.inj hjH)
  · have hj0 : j = 0 := by
      rw [getElem?_flankWord] at hjH
      split_ifs at hjH <;> first | omega | exact BTone.noConfusion (Option.some.inj hjH)
    have := hlast (2 * d + 5) (by rw [length_flankWord]; omega) getElem?_flankWord_last
    omega

private theorem not_bembaSurfaces_flankWord_LL {d : ℕ} :
    ¬ bembaSurfaces (flankWord .L .L .L (2 * d + 4)) (d + 3) := by
  have hnoH : ∀ k, (flankWord BTone.L .L .L (2 * d + 4))[k]? ≠ some BTone.H := fun k ↦ by
    rw [getElem?_flankWord]
    split_ifs <;> first | exact fun h ↦ BTone.noConfusion (Option.some.inj h) | simp
  rintro ⟨-, h | ⟨j, -, hjH, -⟩ | ⟨j, -, hjH, -⟩⟩
  exacts [hnoH _ h, hnoH _ hjH, hnoH _ hjH]

-- Prop. 5.4
theorem bemba_requiresBothSides : RequiresBothSides bemba.map :=
  bemba.requiresBothSides_of_flanks (n := fun d ↦ 2 * d + 4) (t := fun d ↦ d + 3)
    (fun d ↦ by omega) (fun d ↦ by omega) (fun d ↦ bembaSurfaces_flankWord_HL)
    (fun d ↦ not_bembaSurfaces_flankWord_LL) (fun d ↦ not_bembaSurfaces_flankWord_HH)

-- Prop. 5.4
theorem bemba_not_bmrsWeaklyDeterministic : ¬ IsBmrsWeaklyDeterministic bemba.map :=
  not_isBmrsWeaklyDeterministic_of_requiresBothSides bemba_requiresBothSides

/-! ### LHOL stress as a simultaneous application (§5.2)

Leftmost-heavy-otherwise-leftmost stress in Lushootseed, Example 2.9: stress the leftmost
heavy syllable, else the leftmost syllable. The backward program stresses a heavy with no
heavy to its left; the forward program stresses an initial light with no heavy to its right.
No syllable is underlyingly stressed, so the input predicate is constantly false and ⊙
collapses to the disjunction (5.15) of the two programs, the program of [koser-jardine-2020]. -/

/-- A syllable is heavy or light. -/
inductive Syll
  | H | L
  deriving DecidableEq, Repr

/-- The backward stress program has two heads, `noHL` being (5.8), no heavy anywhere to the
left. -/
inductive LHead
  | noHL | stressL
  deriving DecidableEq, Fintype

/-- The forward stress program has two heads, `noHR` being (5.9), no heavy anywhere to the
right. -/
inductive RHead
  | noHR | stressR
  deriving DecidableEq, Fintype

/-- The backward program, (5.8) and (5.12), stresses a heavy with no heavy to its left. -/
def lholL : Program Syll LHead
  | .noHL => .ite (.initial x) .tru (.ite (.label {.H} x.pred) .fls (.call .noHL x.pred))
  | .stressL => (Expr.label {.H} x).and (.call .noHL x)

/-- The forward program, (5.9) and (5.11), stresses an initial light with no heavy to its
right. -/
def lholR : Program Syll RHead
  | .noHR => .ite (.final x) .tru (.ite (.label {.H} x.succ) .fls (.call .noHR x.succ))
  | .stressR => (Expr.label {.L} x).and ((Expr.initial x).and (.call .noHR x))

theorem lholL_backward : lholL.Backward := by decide

theorem lholR_forward : lholR.Forward := by decide

/-- The stress pattern the ⊙ of the two programs assigns to a word, position by position, is
the disjunction (5.15), there being no underlying stress. -/
def lholStress (w : List Syll) : List (Option Bool) :=
  (List.range w.length).map fun i ↦
    (lholL.eval w i (.call .stressL x)).bind fun bL ↦
      (lholR.eval w i (.call .stressR x)).map fun bR ↦ combine false bL bR

-- Example 2.9
theorem lholStress_LHLHL :
    lholStress [.L, .H, .L, .H, .L] =
      [some false, some true, some false, some false, some false] := by
  decide

-- Example 2.9
theorem lholStress_HHHHH :
    lholStress [.H, .H, .H, .H, .H] =
      [some true, some false, some false, some false, some false] := by
  decide

-- Example 2.9
theorem lholStress_LLLLL :
    lholStress [.L, .L, .L, .L, .L] =
      [some true, some false, some false, some false, some false] := by
  decide

/-! ### Sour Grapes as a conjunctive simultaneous application (§6.3) -/

/-- At a target, Sour Grapes spreads iff a trigger lies to the left and no blocker to the right,
conjoining (6.6) and (6.7) by ⊘ (Def. 6.5). -/
theorem sourGrapes_conjunctive {w : List SG} {i : ℕ} (hm : w[i]? = some .minus) :
    (sourGrapes w)[i]? = some (if combineC false
      (decide (.plus ∈ w.take i)) (decide (.blk ∉ w.drop i)) then .plus else .minus) := by
  rw [sourGrapes, List.getElem?_mapIdx, hm, Option.map_some, combineC_false]
  by_cases hL : .plus ∈ w.take i <;> by_cases hR : .blk ∉ w.drop i <;>
    simp [hL, hR]

end Yolyan2025
