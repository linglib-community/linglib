/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.Transduction
public import Linglib.Data.Examples.Dolatian2020

/-!
# Dolatian (2020): Computational locality of cyclic phonology in Armenian

This file formalizes the analysis of destressed high vowel reduction in Chapters 1 and 2 of
[dolatian-2020] and its computational rendering in Chapter 6. Armenian stress falls on the
rightmost full vowel of a word, (1), and is reassigned as each suffix is added; a high vowel
that was stressed in the base and loses stress in the derivative, and only such a vowel,
reduces, deleting when the cluster it leaves is syllabifiable and otherwise becoming schwa,
(46). Reduction is cyclic without bound, (5) and (48): each morpheme may trigger a new round
of stress shift and reduction. It is stratal, after [kiparsky-1982]: in Western Armenian the
derivational suffixes that build morphological stems trigger the stem-level cophonology of
stress shift with reduction, while the inflectional suffixes that build morphological words
trigger the word-level cophonology of stress shift alone, (7) to (9). And it is prosodic: in
Eastern Armenian vowel-initial inflection reduces as well, (10) and (65), because onset
maximization resyllabifies the stem-final consonant and misaligns the Prosodic Stem of
[downing-1999] that the morphological stem maps to; the misaligned stem expands over the
suffix and triggers a cophonology of its own, which reduces high vowels in Eastern but not in
Western Armenian and reduces the diphthong *uj* in neither, (76) and (78). The plural
allomorphy of (66), *-er* after monosyllables and *-ner* after polysyllables, thereby decides
whether a plural reduces its base. Reduction itself is a quantifier-free logical transduction,
§6.6.1, and so local in the sense of [chandlee-2014]: given the destressing diacritic,
deletion and schwa are read off two segments on either side of the target.

## Implementation notes

Segments are kept at the granularity the analysis reads: consonant, high vowel, other full
vowel, the diphthong *uj*, and schwa, so that *u* and *i* are one symbol and the segmental
detail of [vaux-1998] is not represented. Stress is computed as the position of the rightmost
full vowel rather than as the logical transduction of Chapter 5, and destressing compares that
position across a cycle; the reduction step is the transduction `dhr`, run on the string with
the destressed vowel marked, so a cycle composes a stress function with a quantifier-free map,
and the domain label that the dissertation's SETTINGS constant supplies to the reduction
formulas is the cophonology argument of `reduce`. Syllabifiability, (46), is the condition
that the destressed vowel be flanked by single consonants that themselves neighbour nuclei.
Prosodic Stem misalignment is read off the stem-final consonant and the suffix-initial vowel,
without a syllabification. The foot and recursive prosodic word alternatives of §2.5.3, the
lexical exceptions of (72) and the variation of §2.7.3, and the compound bracketing paradox of
Chapter 3 are not formalized.

## TODO

The complex-coda clause of (46), a second consonant before the target licensed when the two
form a falling-sonority coda, needs a sonority scale over consonants; with one consonant
symbol, `dhr` gives schwa where the dissertation deletes, as in *jergír* ~ *jergr-a-kúnt*, (17).

## References

* [dolatian-2020]
* [kiparsky-1982]
* [downing-1999]
* [vaux-1998]
* [chandlee-2014]
-/

@[expose] public section

namespace Dolatian2020

open Subregular

/-! ### Segments and stress, (1) -/

/-- Segments at the granularity of the analysis: a consonant, a high vowel, another full vowel,
the diphthong *uj*, and schwa. -/
inductive Seg
  | c
  | h
  | v
  | uj
  | schwa
  deriving DecidableEq, Repr

/-- A full vowel bears stress: a high or other full vowel or the diphthong, not schwa. -/
def Seg.Full : Seg → Prop
  | .h | .v | .uj => True
  | _ => False

/-- A syllable nucleus: any vowel, schwa included. -/
def Seg.Nucleus : Seg → Prop
  | .c => False
  | _ => True

instance : DecidablePred Seg.Full := fun s ↦ by cases s <;> unfold Seg.Full <;> infer_instance

instance : DecidablePred Seg.Nucleus := fun s ↦ by
  cases s <;> unfold Seg.Nucleus <;> infer_instance

/-- The position of the stressed vowel, the rightmost full vowel, (1). -/
def stress (w : List Seg) : Option ℕ := (w.findIdxs (decide <| Seg.Full ·)).getLast?

/-! ### Reduction as a quantifier-free transduction, (46) and §6.6.1 -/

def x : Walk := .var

/-- The guard that a term reads a nucleus not carrying the destressing mark. -/
def nucleusAt (t : Walk) : WindowFormula (Seg × Bool) :=
  .label (.h, false) t ⊔ .label (.v, false) t ⊔ .label (.uj, false) t ⊔ .label (.schwa, false) t

/-- The context in which deletion leaves a syllabifiable cluster, (46): a nucleus and a single
consonant before the target and a single consonant and a nucleus after it. -/
def deletable : WindowFormula (Seg × Bool) :=
  nucleusAt x.pred.pred ⊓ .label (.c, false) x.pred ⊓ .label (.c, false) x.succ ⊓
    nucleusAt x.succ.succ

/-- Destressed high vowel reduction as a quantifier-free transduction, (46): the destressed high
vowel, marked `true`, is deleted where deletion is licensed and becomes schwa elsewhere; every
other segment is kept, its mark dropped. -/
def dhr : Transduction (Seg × Bool) Seg :=
  ⟨[(WindowFormula.label (.h, true) x ⊓ deletable, []), (.label (.h, true) x, [.schwa])] ++
    [Seg.c, .h, .v, .uj, .schwa].flatMap fun s ↦
      [(.label (s, false) x, [s]), (.label (s, true) x, [s])]⟩

/-- The string with the destressed position marked. -/
def mark (w : List Seg) (p : ℕ) : List (Seg × Bool) := w.mapIdx fun n s ↦ (s, decide (n = p))

/-! ### Cophonologies, (76) -/

/-- The reductions a cophonology applies: destressed high vowel reduction and destressed
diphthong reduction. -/
structure Cophonology where
  /-- Destressed high vowel reduction applies. -/
  dhr : Bool
  /-- Destressed diphthong reduction applies. -/
  ddr : Bool
  deriving DecidableEq, Repr

/-- The stem-level cophonology, triggered by derivation: both reductions. -/
def stemLevel : Cophonology := ⟨true, true⟩

/-- The word-level cophonology, triggered by inflection: stress shift alone. -/
def wordLevel : Cophonology := ⟨false, false⟩

/-- The two standard dialects, which share the morphology and the Prosodic Stem and differ in
its cophonology. -/
inductive Dialect
  | eastern
  | western
  deriving DecidableEq, Repr

/-- The Prosodic Stem cophonology, (76): high vowel reduction without diphthong reduction in
Eastern Armenian, stress shift alone in Western Armenian. -/
def Dialect.pstemLevel : Dialect → Cophonology
  | .eastern => ⟨true, false⟩
  | .western => wordLevel

/-- Apply a cophonology's reductions to the destressed vowel at `p`. -/
def reduce (c : Cophonology) (w : List Seg) (p : ℕ) : List Seg :=
  match w[p]? with
  | some .h => if c.dhr then dhr.apply (mark w p) else w
  | some .uj => if c.ddr then w.set p .h else w
  | _ => w

/-! ### Strata, the Prosodic Stem and the cycle, (9), (14) and (78) -/

/-- Whether a suffix builds a morphological stem, derivation, or a morphological word,
inflection. -/
inductive Stratum
  | stem
  | word
  deriving DecidableEq, Repr

/-- A suffix: its segments and the stratum it triggers. -/
structure Suffix where
  /-- The segments of the suffix. -/
  segs : List Seg
  /-- The stratum the suffix triggers. -/
  stratum : Stratum

/-- The Prosodic Stem mapped from the base is misaligned from the syllables by a vowel-initial
suffix after a consonant-final base, §2.5.3: onset maximization resyllabifies the final
consonant, and the stem expands over the suffix. -/
def Misaligned (base suf : List Seg) : Prop :=
  base.getLast? = some .c ∧ ∃ s ∈ suf.head?, s.Nucleus

instance (base suf : List Seg) : Decidable (Misaligned base suf) := by
  unfold Misaligned; infer_instance

/-- The cophonology a cycle triggers, (76) and (78): the stem-level for derivation, and for
inflection the Prosodic Stem cophonology of the dialect when the stem is misaligned and the
word-level otherwise. -/
def cophonology (d : Dialect) (base : List Seg) (s : Suffix) : Cophonology :=
  match s.stratum with
  | .stem => stemLevel
  | .word => if Misaligned base s.segs then d.pstemLevel else wordLevel

/-- One cycle: the suffix is spelled out, stress is reassigned, and the vowel stressed in the
base, if it has lost stress, reduces according to the cophonology the cycle triggers. -/
def cycle (d : Dialect) (base : List Seg) (s : Suffix) : List Seg :=
  match stress base with
  | none => base ++ s.segs
  | some p =>
    if stress (base ++ s.segs) = some p then base ++ s.segs
    else reduce (cophonology d base s) (base ++ s.segs) p

/-- The cyclic derivation of a root with its suffixes, in order: unbounded cyclicity, §2.3.2.2. -/
def derive (d : Dialect) (root : List Seg) (sufs : List Suffix) : List Seg :=
  sufs.foldl (cycle d) root

/-- The plural allomorph, (66): *-er* after a monosyllabic base and *-ner* after a polysyllabic
one. -/
def plural (base : List Seg) : Suffix :=
  ⟨if base.countP (decide <| Seg.Nucleus ·) = 1 then [.v, .c] else [.c, .v, .c], .word⟩

/-! ### What the cophonologies exclude -/

variable (base : List Seg) (s : Suffix)

theorem reduce_of_none {c : Cophonology} (h : c.dhr = false) (h' : c.ddr = false)
    (w : List Seg) (p : ℕ) : reduce c w p = w := by
  unfold reduce
  split <;> simp_all

theorem cycle_of_cophonology_eq (d : Dialect) (h : cophonology d base s = wordLevel) :
    cycle d base s = base ++ s.segs := by
  unfold cycle
  rw [h]
  split
  · rfl
  · split
    · rfl
    · exact reduce_of_none rfl rfl _ _

-- (76)
theorem cophonology_western_word (h : s.stratum = .word) :
    cophonology .western base s = wordLevel := by
  simp only [cophonology, h, Dialect.pstemLevel, ite_self]

-- (78)
theorem cophonology_word_of_not_misaligned (d : Dialect) (h : s.stratum = .word)
    (hm : ¬ Misaligned base s.segs) : cophonology d base s = wordLevel := by
  simp only [cophonology, h, ite_eq_right hm]

-- (76)
theorem cophonology_dialect_eq (h : s.stratum = .stem ∨ ¬ Misaligned base s.segs) :
    cophonology .eastern base s = cophonology .western base s := by
  unfold cophonology
  rcases h with h | h
  · rw [h]
  · cases s.stratum
    · rfl
    · rw [ite_eq_right h, ite_eq_right h]

-- (76)
theorem cophonology_word_ddr (d : Dialect) (h : s.stratum = .word) :
    (cophonology d base s).ddr = false := by
  simp only [cophonology, h]
  split <;> cases d <;> rfl

-- (7), (37)
theorem cycle_western_word (h : s.stratum = .word) : cycle .western base s = base ++ s.segs :=
  cycle_of_cophonology_eq base s _ (cophonology_western_word base s h)

-- (10e)
theorem cycle_word_of_not_misaligned (d : Dialect) (h : s.stratum = .word)
    (hm : ¬ Misaligned base s.segs) : cycle d base s = base ++ s.segs :=
  cycle_of_cophonology_eq base s d (cophonology_word_of_not_misaligned base s d h hm)

theorem cycle_dialect_eq (h : s.stratum = .stem ∨ ¬ Misaligned base s.segs) :
    cycle .eastern base s = cycle .western base s := by
  unfold cycle
  rw [cophonology_dialect_eq base s h]

-- (12)
theorem cycle_word_diphthong (d : Dialect) (h : s.stratum = .word) {p : ℕ}
    (hp : stress base = some p) (hd : (base ++ s.segs)[p]? = some .uj) :
    cycle d base s = base ++ s.segs := by
  simp only [cycle, hp]
  split
  · rfl
  · simp [reduce, hd, cophonology_word_ddr base s d h]

/-! ### The forms, (5), (10), (12), (42), (47), (48), (65) and (66) -/

/-- *amusín* 'husband': a.mu.sín. -/
def amusin : List Seg := [.v, .c, .h, .c, .h, .c]

/-- *-utjun*, derivational. -/
def utjun : Suffix := ⟨[.h, .c, .c, .h, .c], .stem⟩

/-- *-anal*, derivational inchoative. -/
def anal : Suffix := ⟨[.v, .c, .v, .c], .stem⟩

/-- *-ov*, the instrumental. -/
def ov : Suffix := ⟨[.v, .c], .word⟩

/-- *-ner*, the plural after polysyllables. -/
def ner : Suffix := ⟨[.c, .v, .c], .word⟩

-- (7a), (77)
theorem amusin_utjun (d : Dialect) :
    derive d amusin [utjun] = [.v, .c, .h, .c, .c, .h, .c, .c, .h, .c] := by
  cases d <;> decide

-- (10c), (10d)
theorem amusin_ov :
    derive .eastern amusin [ov] = [.v, .c, .h, .c, .c, .v, .c] ∧
      derive .western amusin [ov] = amusin ++ ov.segs := by
  decide

-- (10e)
theorem amusin_ner (d : Dialect) : derive d amusin [ner] = amusin ++ ner.segs :=
  cycle_word_of_not_misaligned amusin ner d rfl (by decide)

-- (47)
theorem forms_47 :
    derive .western [.c, .h, .c, .v, .c, .c] [anal] = [.c, .h, .c, .v, .c, .c] ++ anal.segs ∧
      derive .western [.c, .v, .c, .c, .h, .c, .c] [anal] =
        [.c, .v, .c, .c, .schwa, .c, .c] ++ anal.segs ∧
      derive .western amusin [anal] = [.v, .c, .h, .c, .c] ++ anal.segs := by
  decide

-- (42b)
theorem azniv_utjun :
    derive .western [.v, .c, .c, .h, .c] [utjun] = [.v, .c, .c, .schwa, .c] ++ utjun.segs := by
  decide

-- (5a)
theorem dzin :
    derive .western [.c, .h, .c] [⟨[.h, .c, .c], .stem⟩] = [.c, .schwa, .c, .h, .c, .c] ∧
      derive .western [.c, .h, .c] [⟨[.h, .c, .c], .stem⟩, ⟨[.v, .c, .v, .c], .stem⟩] =
        [.c, .schwa, .c, .schwa, .c, .c, .v, .c, .v, .c] := by
  decide

-- (48a)
theorem azk :
    derive .western [.v, .c, .c] [⟨[.v, .c, .h, .c], .stem⟩, ⟨[.v, .c, .v, .c], .stem⟩] =
      [.v, .c, .c, .v, .c, .c, .v, .c, .v, .c] := by
  decide

-- (12), (62)
theorem zerujts :
    derive .eastern [.c, .schwa, .c, .uj, .c] [⟨[.v, .c], .stem⟩] =
        [.c, .schwa, .c, .h, .c, .v, .c] ∧
      derive .eastern [.c, .schwa, .c, .uj, .c] [ov] = [.c, .schwa, .c, .uj, .c] ++ ov.segs := by
  decide

-- (66)
theorem plurals :
    derive .eastern [.c, .h, .c, .c] [plural [.c, .h, .c, .c]] = [.c, .schwa, .c, .c, .v, .c] ∧
      derive .eastern amusin [plural amusin] = amusin ++ ner.segs ∧
      derive .eastern [.c, .h, .c, .c] [plural [.c, .h, .c, .c], ov] =
        [.c, .schwa, .c, .c, .v, .c] ++ ov.segs ∧
      derive .eastern amusin [plural amusin, ov] = amusin ++ ner.segs ++ ov.segs := by
  decide

-- (65)
theorem western_cases :
    derive .western amusin [ov] = amusin ++ ov.segs ∧
      derive .western amusin [⟨[.h], .word⟩] = amusin ++ [.h] :=
  ⟨cycle_western_word amusin ov rfl, cycle_western_word amusin ⟨[.h], .word⟩ rfl⟩

end Dolatian2020
