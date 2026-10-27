/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.Mealy
public import Linglib.Phonology.Subregular.ISL
public import Linglib.Phonology.Subregular.OSL
public import Linglib.Core.Computability.Subsequential
public import Linglib.Phonology.Subregular.Dependence
public import Linglib.Core.Computability.Bimachine
public import Studies.LamontOHaraSmith2019
public import Studies.McCollumEtAl2020

/-!
# Meinhardt, Mai, Baković and McCollum (2024): Weak Determinism and ATR Harmony

This file formalizes the Maasai case of Meinhardt, Mai, Baković and McCollum, who tighten
the weakly deterministic function class of Heinz and Lai by an explicit interaction
condition. Bidirectional iterative ATR harmony in Maasai is attested and weakly
deterministic, an unbounded semiambient pattern in which every target depends on one side
at a time, so its two contradirectional subsequential passes do not interact; Turkana,
identical but for exceptionally dominant retracted suffix vowels, is attested and
non-deterministic, an unbounded circumambient pattern in which some targets depend on both
sides at once. Dominance is an underlying specification of the spreading value on vowels,
carried by roots and suffixes alike. The rightward spreading pass is output-strictly-local
after Chandlee, Eyraud and Heinz, the bidirectional dominant–recessive map is weakly
deterministic through a non-interacting bimachine (`maasai_isNonInteractingBimachineComputable`)
with two-sided unbounded dependence (`maasai_twoSidedUnboundedDependence`) but without
requiring both sides at once (`maasai_not_requiresBothSides`), the boundary the paper draws.
Tutrugbu's conditional blocking, the paper's (3), and unbounded tonal plateauing, its (2), lie on
the other side: each requires both sides, so neither is semiambient (`tutrugbu_not_semiambient`)
or computed by a non-interacting bimachine. Plateauing is nonetheless weakly deterministic in
Heinz and Lai's sense, by the phonotactic code of §5.2, so their class is not contained in the
paper's (`exists_isWeaklyDeterministic_not_isNonInteractingBimachineComputable`).

## Implementation notes

The alphabet has four symbols carrying the dominant–recessive distinction; the bidirectional
map is modelled directly, raising a recessive vowel when a dominant one occurs anywhere,
rather than as a two-pass composition, and the opaque low vowel, the re-paired low vowel,
glide effects, and the Turkana half of the paper are not represented.

Weak determinism is rendered by the change-based reading of Def. 5: a non-interacting bimachine
licenses every change by one side alone (`IsNonInteractingBimachineComputable`). Def. 6 read
literally asks the same of unchanged cells, and the Maasai bimachine of Fig. 8 fails it: at a
recessive vowel with `q1` on both sides the output is the vowel itself, and moving either state
alone to `q2` changes it.

## References

* [meinhardt-mai-bakovic-mccollum-2024]
* [heinz-lai-2013]
* [chandlee-eyraud-heinz-2015]
* [wilson-2006]
* [mccollum-bakovic-mai-meinhardt-2020]
* [lamont-ohara-smith-2019]
-/

@[expose] public section

namespace MeinhardtEtAl2024

open Subregular

/-- A minimal alphabet captures the dominance-vs-recessive distinction that drives Maasai ATR
harmony (p. 1203). Four symbols stand in for the relevant phonological contrasts.

* `recL` — a recessive [-ATR] vowel (e.g., /ɪ/, /ʊ/), surfacing as
  [-ATR] absent harmony and raising to [+ATR] under spread.
* `recH` — a recessive vowel surfacing [+ATR] (e.g., /i/, /u/), the
  raised form of `recL`, and transparent to further spread.
* `dom` — a dominant vowel, underlyingly specified [+ATR] and the trigger
  of spreading (the paper's load-bearing distinction).
* `a` — the opaque /a/. Blocks spread.

Consonants are omitted as they are transparent to the harmony. -/
inductive Seg
  | recL
  | recH
  | dom
  | a
  deriving DecidableEq, Repr

instance : Fintype Seg where
  elems := {.recL, .recH, .dom, .a}
  complete := fun x ↦ by cases x <;> simp

namespace Seg

/-- Whether the segment is a [+ATR] vowel after surface realisation, which holds of `dom` and
`recH` and fails of `recL` (until raised by spread) and of `a`. -/
def isPlusATR : Seg → Bool
  | .recH | .dom => true
  | _ => false

/-- The surface form of a segment under spreading [+ATR], which raises recessive [-ATR] vowels
and passes everything else through unchanged, including the opaque /a/. -/
def raise : Seg → Seg
  | .recL => .recH
  | s => s

end Seg

/-- **OSL rule encoding rightward [+ATR] spreading from a dominant root.**

With k = 2 the output decision at each position depends on the
**single immediately preceding output symbol**, as in the canonical OSL fragment of
phonological maps of Chandlee, Eyraud and Heinz. The rule emits as follows.

* Current input is `dom` → emit `recH` (dominant always surfaces as
  [+ATR]).
* Current input is `a` → emit `a` (opaque, blocks spread; the next
  position's output context will be `a`, not a +ATR vowel).
* Current input is `recH` → emit `recH` (already +ATR, passes through).
* Current input is `recL` and previous output was `recH` → emit `recH`
  (spread continues).
* Current input is `recL` otherwise → emit `recL` (no spread to here).

Single-direction iterative spreading patterns are OSL but not ISL, after Chandlee, Eyraud and
Heinz, because the output decision depends on the
*output* history (how far spread has propagated) rather than the *input*
history alone (`rightwardATR_osl_not_isLeftInputStrictlyLocal`). -/
def rightwardATR_osl : OSLRule 2 Seg Seg where
  windowOutput outputWindow currentInput :=
    match currentInput, outputWindow with
    | .a, _ => [.a]
    | .dom, _ => [.recH]
    | .recH, _ => [.recH]
    | .recL, .recH :: _ => [.recH]
    | .recL, _ => [.recL]

/-- The dominant root triggers spread to the following recessive vowel (Ex 1a-i, rightward
half), in a toy encoding of the rightward portion of /kɪ-√noŋ-ʊ/ → [ki-√noŋ-u] as input
`[dom, recL]` and output `[recH, recH]`. -/
example : rightwardATR_osl.apply [.dom, .recL] = [.recH, .recH] := by decide

/-- Spread continues across multiple recessive vowels (Ex 1a-ii, rightward half). -/
example : rightwardATR_osl.apply [.dom, .recL, .recL] = [.recH, .recH, .recH] := by
  decide

/-- The opaque /a/ blocks rightward spread, so recessive vowels after it remain [-ATR]. -/
example : rightwardATR_osl.apply [.dom, .a, .recL] = [.recH, .a, .recL] := by
  decide

/-- Without a dominant trigger, a string of recessive vowels passes through unchanged. -/
example : rightwardATR_osl.apply [.recL, .recL] = [.recL, .recL] := by decide

theorem rightwardATR_osl_isLeftOutputStrictlyLocal :
    IsLeftOutputStrictlyLocal 2 rightwardATR_osl.apply :=
  rightwardATR_osl.isLeftOutputStrictlyLocal_apply

private theorem rightwardATR_osl_apply_dom_replicate (n : ℕ) :
    rightwardATR_osl.apply (.dom :: List.replicate n .recL) = List.replicate (n + 1) .recH := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', ← List.cons_append, OSLRule.apply_append_singleton, ih,
      List.replicate_succ' (n := n + 1), List.replicate_succ', List.rtake_concat_succ,
      List.rtake_zero, List.nil_append]
    rfl

private theorem rightwardATR_osl_apply_replicate (n : ℕ) :
    rightwardATR_osl.apply (List.replicate n .recL) = List.replicate n .recL := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', OSLRule.apply_append_singleton, ih]
    cases n with
    | zero => rfl
    | succ m =>
      rw [List.replicate_succ', List.rtake_concat_succ, List.rtake_zero, List.nil_append]
      rfl

theorem rightwardATR_osl_not_isLeftInputStrictlyLocal (k : ℕ) :
    ¬ IsLeftInputStrictlyLocal k rightwardATR_osl.apply := fun h ↦ by
  have hw : ∀ s : Seg, (s :: List.replicate (k - 1) .recL).rtake (k - 1) =
      List.replicate (k - 1) .recL := fun s ↦ by
    simpa using List.rtake_append_length (l₁ := [s]) (l₂ := List.replicate (k - 1) Seg.recL)
  have e := congrFun (h.factorsThrough_residual (a := .dom :: List.replicate (k - 1) .recL)
    (b := .recL :: List.replicate (k - 1) .recL) (by simp only [hw])) [.recL]
  rw [Function.residual_eq_drop (h.isPrefix _), Function.residual_eq_drop (h.isPrefix _)] at e
  simp only [List.cons_append, ← List.replicate_succ',
    rightwardATR_osl_apply_dom_replicate, ← List.replicate_succ,
    rightwardATR_osl_apply_replicate, List.length_replicate, List.drop_replicate,
    Nat.add_sub_cancel_left] at e
  exact absurd e (by decide)

theorem rightwardATR_osl_isLeftSubsequential :
    IsLeftSubsequential rightwardATR_osl.apply :=
  rightwardATR_osl_isLeftOutputStrictlyLocal.isLeftSubsequential

/-! ### Bidirectional Maasai harmony — weakly deterministic (faithful)

Maasai dominant-recessive ATR harmony spreads [+ATR] from a dominant root to recessive
vowels on *both* sides. Modelled here in its non-opaque core: a recessive `recL` raises
to `recH` iff the word contains a dominant vowel anywhere (`maasai`). This is a *union*
of two independent spreading passes, so it is **weakly deterministic**
(the paper's unbounded *semiambient*): the bimachine `maasaiBM`
tracks a dominant seen on each side and its output is literally a `unite` of one-sided
rules. A recessive's surface ATR still co-varies with information unboundedly far on
either side, so `maasai` satisfies `TwoSidedUnboundedDependence` — as does Tutrugbu. The
contrast is exactly the WD/ND boundary the paper draws: only Tutrugbu is *circumambient*,
needing both sides at once (`RequiresBothSides`), which Maasai never does. -/

open Subregular

/-- The word contains a dominant trigger. -/
def hasDom (xs : List Seg) : Bool := xs.any (· == .dom)

/-- Bidirectional dominant-recessive harmony in its non-opaque core, under which a recessive
raises iff the word has a dominant trigger anywhere. -/
def maasai (xs : List Seg) : List Seg :=
  xs.map (fun s ↦ if hasDom xs && s == .recL then .recH else s)

/-- The non-interacting bimachine, whose state on each side tracks a dominant seen on that
side, raising a recessive if *either* side has one as a union of one-sided rules. -/
def maasaiBM : Bimachine Bool Bool Seg Seg :=
  .ofFlags (· == .dom) (· == .dom) fun l s r ↦ if (l || r) && s == .recL then .recH else s

theorem maasaiBM_isNonInteracting : maasaiBM.IsNonInteracting :=
  ⟨⟨fun l s ↦ if l && s == .recL then .recH else s,
    fun r s ↦ if r && s == .recL then .recH else s,
    by decide, by intro l s r; cases s <;> cases l <;> cases r <;> rfl⟩⟩

private theorem hasDom_split (xs : List Seg) (i : ℕ) (hi : i < xs.length) :
    hasDom xs = (hasDom (xs.take i) || hasDom (xs.drop (i + 1)) || (xs[i] == .dom)) := by
  simp only [hasDom]
  have heq : xs = xs.take i ++ [xs[i]] ++ xs.drop (i + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hi,
      List.take_append_drop]
  conv_lhs => rw [heq]
  simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  cases (xs.take i).any (· == .dom) <;> cases (xs.drop (i + 1)).any (· == .dom) <;>
    cases (xs[i] == Seg.dom) <;> rfl

private theorem maasaiBM_cell_eq (xs : List Seg) (i : ℕ) (hi : i < xs.length) :
    (if (((xs.take i).any (· == .dom) || (xs.drop (i + 1)).any (· == .dom))
        && xs[i] == .recL) then Seg.recH else xs[i])
    = if hasDom xs && xs[i] == .recL then .recH else xs[i] := by
  rw [hasDom_split xs i hi]
  cases xs[i] <;> simp [hasDom]

theorem maasaiBM_run : maasaiBM.run = maasai := by
  funext xs
  apply List.ext_getElem?
  intro i
  rw [maasaiBM, Bimachine.getElem?_ofFlags_run]
  rcases lt_or_ge i xs.length with hi | hi
  · rw [List.getElem?_eq_getElem hi, Option.map_some, maasaiBM_cell_eq xs i hi]
    simp only [maasai, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, hasDom]
  · rw [List.getElem?_eq_none hi, Option.map_none]
    simp only [maasai, List.getElem?_map, List.getElem?_eq_none (by simpa using hi),
      Option.map_none]

theorem maasai_isNonInteractingBimachineComputable : IsNonInteractingBimachineComputable maasai :=
  maasaiBM_run ▸ maasaiBM.isNonInteractingBimachineComputable maasaiBM_isNonInteracting

/-- **Maasai has two-sided unbounded dependence** — at every distance, a medial
recessive's ATR flips under a dominant placed far to the left *or* far to the right,
each side alone sufficing. Tutrugbu satisfies this too
(`McCollumEtAl2020.tutrugbu_twoSidedUnboundedDependence`), but Maasai does *not*
`RequiresBothSides`, so it stays weakly deterministic. The paper's positive
classification of Maasai as unbounded *semiambient*, with every target fixed by information
from at most one side, is the stronger claim `maasai_semiambient`. -/
theorem maasai_twoSidedUnboundedDependence : TwoSidedUnboundedDependence maasai := by
  refine .of_flanks (fill := Seg.recL) (xOn := Seg.recL) (yOn := Seg.recL)
    (xOff := Seg.dom) (yOff := Seg.dom)
    (n := fun d ↦ 2 * d + 1) (t := fun d ↦ d + 1)
    (fun d ↦ by omega) (fun d ↦ by omega) (fun d ↦ ?_) (fun d ↦ ?_) <;>
  · have hb : hasDom (flankWord Seg.recL Seg.recL Seg.recL (2 * d + 1)) = false := by
      simp [hasDom, flankWord]
    have hp : ∀ y, hasDom (flankWord Seg.dom Seg.recL y (2 * d + 1)) = true := fun y ↦ by
      simp [hasDom, flankWord]
    have hp' : ∀ x, hasDom (flankWord x Seg.recL Seg.dom (2 * d + 1)) = true := fun x ↦ by
      simp [hasDom, flankWord]
    simp only [maasai, List.getElem?_map,
      getElem?_flankWord_mid (show 0 < d + 1 by omega) (show d + 1 ≤ 2 * d + 1 by omega),
      hb, hp, hp']
    decide

theorem maasai_semiambient : OneSidedChanges maasai :=
  maasai_isNonInteractingBimachineComputable.oneSidedChanges

theorem maasai_not_requiresBothSides : ¬ RequiresBothSides maasai := fun h ↦
  h.not_isNonInteractingBimachineComputable maasai_isNonInteractingBimachineComputable

theorem maasai_not_mealyComputable : ¬ IsMealyComputable maasai := fun h ↦
  maasai_twoSidedUnboundedDependence.unboundedDependence .right h.boundedDependence_right

theorem maasai_not_leftSubsequential : ¬ IsLeftSubsequential maasai :=
  maasai_twoSidedUnboundedDependence.not_isSubsequential (fun _ ↦ by simp [maasai]) .left

/-! ### Tutrugbu

Tutrugbu's conditional blocking, the paper's (3), is unbounded circumambient (Def. 2). It
requires both sides, so some change it makes is licensed by neither side alone and no
non-interacting bimachine computes it. -/

/-- Tutrugbu ATR harmony is not semiambient (Def. 3), since some change it makes is licensed
by neither side alone. -/
theorem tutrugbu_not_semiambient : ¬ OneSidedChanges McCollumEtAl2020.tutrugbu.map :=
  McCollumEtAl2020.tutrugbu_requiresBothSides.not_oneSidedChanges

theorem tutrugbu_not_isNonInteractingBimachineComputable :
    ¬ IsNonInteractingBimachineComputable McCollumEtAl2020.tutrugbu.map :=
  McCollumEtAl2020.tutrugbu_requiresBothSides.not_isNonInteractingBimachineComputable

/-! ### Unbounded tonal plateauing

Plateauing, the paper's (2), is unbounded circumambient (Def. 2): it requires both sides, so no
non-interacting bimachine computes it. Yet it is weakly deterministic in Heinz and Lai's sense,
by the phonotactic code of Lamont, O'Hara and Smith that §5.2 and Fig. 12 take up: their first
pass is length- and alphabet-preserving and still tells the second pass what lies beyond its
reach. -/

theorem utp_not_isNonInteractingBimachineComputable :
    ¬ IsNonInteractingBimachineComputable Tone.utp.map :=
  Tone.utp.requiresBothSides.not_isNonInteractingBimachineComputable

theorem exists_isWeaklyDeterministic_not_isNonInteractingBimachineComputable :
    ∃ f : List Tone.AssociationState → List Tone.AssociationState,
      IsWeaklyDeterministic f ∧ ¬ IsNonInteractingBimachineComputable f :=
  ⟨Tone.utp.map, LamontOHaraSmith2019.utp_isWeaklyDeterministic,
    utp_not_isNonInteractingBimachineComputable⟩

end MeinhardtEtAl2024
