/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Melody
public import Linglib.Morphology.Word.Tree

/-!
# Laoide-Kemp (2026): Strict modularity at the morphosyntax-phonology interface

This file formalizes the analysis of [laoide-kemp-2026] of the Irish historic-tense particle
*d'*, which appears before vowel-initial and lenited *f*-initial verbs but not before other
consonants ((11)), an apparent paradox for the autosegmental account of initial consonant
mutation, since the particle taken to trigger lenition seems to be inserted only once lenition
has applied. On the paper's account the exponent of historic tense is a floating segment `(d)`
followed by the lenition-inducing bundle `{L}` ((18)): both are inserted in every environment,
`{L}` docks onto the following consonant, deleting the segmental content of an *f* (§2.2), and
`(d)` is pronounced only if it can link to an adjacent skeletal C-slot that is empty and
directly followed by a filled V-slot (§4.1). Over the library's floating autosegmental forms
on a strict-CV skeleton ([lowenstamm-1996]), the historic exponent is prefixed by
concatenation, lenition is the surface delinking of a word-initial *f*, and the docking
condition is read off the surface form: `(d)` surfaces before *ól* and *fág* but not before
*bog* (Figure 1), and never before a past-tense impersonal, whose empty initial CV unit blocks
both lenition and docking (Figure 5, §6.2), the two effects of one piece of structure
(`laoideKemp_fig1_fig5`, `impersonal_blocks_lenition`). The analysis is strictly modular in the
sense of [bermudez-otero-2012]: the morpheme is inserted uniformly and the phonology decides.

## Implementation notes

The segment inventory covers the paper's examples only. Lenition is modelled as the deletion
of *f* alone, the one effect that bears on the distribution of `(d)`, and targets the melody
linked to the leftmost skeletal slot, so the empty CV unit of an impersonal keeps the stem's
*f* out of reach. The infrasegmental-government domains that license `(d)` before the lenited
clusters of (12) (Figure 2, [scheer-1998]), the Munster reanalysis of `(d)` as part of the
lenition bundle (§6.1, Table 3), and the rejected morphosyntactic alternative of §5 are not
modelled.

## TODO

Model Figure 2, the *r*- against *fr*-initial contrast, once a government substrate exists.

## References

* [laoide-kemp-2026]
* [bermudez-otero-2012], [lowenstamm-1996], [gussmann-1986], [ni-chiosain-1991],
  [scheer-1998]
-/

@[expose] public section

namespace LaoideKemp2026

open Autosegmental
open Morphology (Morph)

/-! ### Segments and skeleton -/

/-- The segments of the paper's worked examples. -/
inductive Segment
  /-- Consonant `b`. -/
  | b
  /-- Consonant `g`. -/
  | g
  /-- Consonant `l`. -/
  | l
  /-- Consonant `f`. -/
  | f
  /-- Consonant `r`. -/
  | r
  /-- Consonant `m`. -/
  | m
  /-- Vowel `o`. -/
  | o
  /-- Vowel `ó`. -/
  | ó
  /-- Vowel `á`. -/
  | á
  /-- Vowel `i`. -/
  | i
  /-- Schwa-like vowel `a` (Irish `a`). -/
  | a
  /-- The historic-tense floating segment `(d)`. -/
  | dPrime
  deriving DecidableEq, Repr

/-- The segment *f*, whose content lenition deletes (§2.2). -/
def Segment.isF : Segment → Bool
  | .f => true
  | _  => false

/-- A slot of the strict-CV skeleton ([lowenstamm-1996]). -/
inductive CVKind
  | C
  | V
  deriving DecidableEq, Repr

/-! ### Morphemes

Every tier and skeletal element carries its morpheme: the verb stem, the historic-tense
exponent bearing the floating `(d)`, and the past-tense impersonal exponent bearing the empty
CV unit (§6.2). -/

/-- The verb-stem morpheme (a free word), keyed by orthographic form. -/
def mStem (s : String) : Morph := .root s

/-- The historic-tense exponent, bearing `(d)` and `{L}`. -/
def mHist : Morph := .pref "d'"

/-- The past-tense impersonal exponent (§6.2). -/
def mImpers : Morph := .pref ""

/-! ### Verb stems

A stem is a floating form whose upper tier is the melody, whose lower tier is the CV skeleton,
and whose association lines `(k, j)` link melody element `k` to skeletal slot `j`; on input the
surface state is the underlying one. -/

/-- Build a single-morpheme verb stem from its CV skeleton, melody,
    and association lines. -/
def stemForm (name : String) (skeleton : List CVKind) (mel : List Segment)
    (links : Finset (Nat × Nat)) : Form CVKind Segment Morph :=
  Form.melody (mStem name) mel skeleton links

/-- *bog* 'move', consonant-initial (Figure 1a). -/
def bog : Form CVKind Segment Morph :=
  stemForm "bog" [.C, .V, .C] [.b, .o, .g] {(0, 0), (1, 1), (2, 2)}

/-- *ól* 'drink', vowel-initial (Figure 1b): the initial C-slot is empty underlyingly. -/
def ól : Form CVKind Segment Morph :=
  stemForm "ol" [.C, .V, .C, .V] [.ó, .l] {(0, 1), (1, 2)}

/-- *fág* 'leave', *f*-initial (Figure 1c). -/
def fág : Form CVKind Segment Morph :=
  stemForm "fag" [.C, .V, .C] [.f, .á, .g] {(0, 0), (1, 1), (2, 2)}

/-! ### The exponents

The historic-tense morpheme contributes a floating `(d)` with no skeleton of its own ((18)),
and the past-tense impersonal morpheme an empty CV unit with no melody (Figure 5); each is
prefixed to a stem by concatenation, which shifts the stem's association lines by the prefix's
tier lengths. -/

/-- The historic-tense exponent ((18)): a floating `(d)`, no skeleton, no associations. -/
def historicExponent : Form CVKind Segment Morph := .melody mHist [.dPrime] [] ∅

/-- The past-tense impersonal exponent (§6.2, Figure 5): an empty CV unit, no melody. -/
def impersonalExponent : Form CVKind Segment Morph := .melody mImpers [] [.C, .V] ∅

/-- In the historic-tense form of a stem, `(d)` becomes melody element 0. -/
def withHist (stem : Form CVKind Segment Morph) : Form CVKind Segment Morph :=
  historicExponent.concat stem

/-- The past-tense impersonal of a stem adds an empty CV unit at the left edge. -/
def withImpers (stem : Form CVKind Segment Morph) : Form CVKind Segment Morph :=
  impersonalExponent.concat stem

/-! ### Lenition

Of the effects of lenition only the deletion of a word-initial *f* bears on the distribution of
`(d)` (§2.2, [gussmann-1986], [ni-chiosain-1991]): `{L}` docks onto the initial consonant and
removes its segmental content, leaving the skeletal slot behind. This is a surface delinking of
the *f* from its slot, and it targets the melody linked to the leftmost skeletal slot, so that
behind an empty CV unit (Figure 5) the stem's *f* is out of reach. -/

/-- The melody index of the consonant linked to the leftmost skeletal slot, the target of
`{L}`. -/
def initialConsonantIdx {u : Form CVKind Segment Morph} (c : Candidate u) :
    Option (Fin u.upper.length) :=
  (List.finRange u.upper.length).find? fun k ↦ decide (∃ l ∈ c.links, l.1 = k ∧ l.2.val = 0)

/-- Lenition deletes the melodic content of an *f* on the leftmost skeletal slot on the
surface, leaving the slot empty. -/
def lenite {u : Form CVKind Segment Morph} (c : Candidate u) : Candidate u :=
  match initialConsonantIdx c with
  | some k => if u.upper[k].value = .f then c.deleteTierElem k else c
  | none   => c

/-! ### Docking

`(d)` is pronounced iff, after lenition, the first skeletal slot is an empty C-slot directly
followed by a filled V-slot (§4.1). -/

/-- The configuration that licenses the docking of `(d)` on the surface has slot 0 an empty
C-slot and slot 1 a filled V-slot (§4.1). -/
def dDockable {u : Form CVKind Segment Morph} (c : Candidate u) : Prop :=
  ∃ i₀ i₁ : Fin u.lower.length, i₀.val = 0 ∧ i₁.val = 1 ∧
    u.lower[i₀].value = .C ∧ ¬ c.IsLinkedLower i₀ ∧
    u.lower[i₁].value = .V ∧ c.IsLinkedLower i₁

instance {u : Form CVKind Segment Morph} (c : Candidate u) : Decidable (dDockable c) :=
  inferInstanceAs (Decidable (∃ _ _, _))

/-- `(d)` surfaces in a historic-tense form iff the lenited form licenses its docking. -/
def dPrimeSurfaces {u : Form CVKind Segment Morph} (c : Candidate u) : Prop :=
  dDockable (lenite c)

instance {u : Form CVKind Segment Morph} (c : Candidate u) : Decidable (dPrimeSurfaces c) :=
  inferInstanceAs (Decidable (dDockable _))

/-! ### Figure 1

In every historic-tense form `(d)` is melody element 0 and floating before docking. -/

/-- `(d)` is floating in a historic-tense form before docking. -/
theorem dPrime_floating_bog : (Candidate.input (withHist bog)).IsFloating ⟨0, by decide⟩ := by
  decide

/-- In Figure 1a, *bog* → *bhog*, the first C-slot is occupied and lenition leaves a segment
in it, so `(d)` cannot dock ((11c)). -/
theorem bog_no_dPrime : ¬ dPrimeSurfaces (.input (withHist bog)) := by decide

/-- In Figure 1b, *ól* → *d' ól*, the first C-slot is empty underlyingly, `{L}` has nothing to
dock onto, and `(d)` links ((11a)). -/
theorem ól_yes_dPrime : dPrimeSurfaces (.input (withHist ól)) := by decide

/-- In Figure 1c, *fág* → *d' fhág*, lenition deletes the *f*, leaving the first C-slot empty
on the surface, and `(d)` links ((11b)). -/
theorem fág_yes_dPrime : dPrimeSurfaces (.input (withHist fág)) := by decide

/-! ### Figure 5

A past-tense impersonal carries an empty CV unit at its left edge (§6.2), which does double
duty: `{L}` finds no consonant to dock onto, and the empty C-slot is followed by an empty
V-slot, so `(d)` cannot link either ((27)). -/

/-- Figure 5a, *bogadh*, has no `(d)`. -/
theorem bogadh_no_dPrime : ¬ dPrimeSurfaces (.input (withHist (withImpers bog))) := by decide

/-- In Figure 5b, *óladh*, the empty V-slot of the prefix blocks docking although the verb is
vowel-initial. -/
theorem óladh_no_dPrime : ¬ dPrimeSurfaces (.input (withHist (withImpers ól))) := by decide

/-- In Figure 5c, *fágadh*, the empty C-slot keeps `{L}` from the stem's *f*, and the empty
V-slot blocks `(d)`. -/
theorem fágadh_no_dPrime : ¬ dPrimeSurfaces (.input (withHist (withImpers fág))) := by decide

/-- In the historic tense `(d)` surfaces before a vowel-initial or *f*-initial verb and not
before a consonant-initial one, and never before a past-tense impersonal (Figures 1 and 5). -/
theorem laoideKemp_fig1_fig5 :
    (¬ dPrimeSurfaces (.input (withHist bog)) ∧ dPrimeSurfaces (.input (withHist ól)) ∧
      dPrimeSurfaces (.input (withHist fág))) ∧
    (¬ dPrimeSurfaces (.input (withHist (withImpers bog))) ∧
      ¬ dPrimeSurfaces (.input (withHist (withImpers ól))) ∧
      ¬ dPrimeSurfaces (.input (withHist (withImpers fág)))) :=
  ⟨⟨bog_no_dPrime, ól_yes_dPrime, fág_yes_dPrime⟩,
   ⟨bogadh_no_dPrime, óladh_no_dPrime, fágadh_no_dPrime⟩⟩

/-- Seen from the other side of Figure 5, the empty CV unit leaves `{L}` no consonant to dock
onto, so an impersonal resists lenition even after a lenition-triggering particle ((26b)). -/
theorem impersonal_blocks_lenition : initialConsonantIdx (.input (withImpers fág)) = none := by
  decide

end LaoideKemp2026
