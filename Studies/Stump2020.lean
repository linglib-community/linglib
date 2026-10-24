module

public import Linglib.Morphology.Paradigm.Function
public import Mathlib.Tactic.DeriveFintype

/-!
# Stump (2020): Paradigm Function Morphology

This file formalizes the Old English paradigm with which Stump's survey of Paradigm
Function Morphology illustrates the framework: the finite forms of the weak verb HIERAN
'hear', run on the PFM engine of `Morphology.Paradigm.Function`. The paradigm's exploded
segmentation is three affix blocks, the past formative, the theme vowel and agreement
(`blockI`, `blockII`, `blockIII`), with the Identity Function Default filling empty
positions, so that the bare imperative is the default firing through every block and the
past forms compose the past formative, the theme vowel and the agreement suffix
(`hieranPF`).

## Implementation notes

Only the past cells and the agreement-suffixed present plural are decided; the present
theme-vowel conditioning across the full paradigm needs block rules the survey's figure
does not legibly give, and the elision of the theme vowel before the present plural suffix
is phonological and not modelled. The survey's Kashmiri morphomic tense is formalized with
its originating work in `Studies/Stump2016.lean`, and its Swahili rule conflation is left
to future work.

## References

* [stump-2020]
* [bonami-stump-2016]
-/

@[expose] public section

namespace Stump2020

open Morphology Morphology.Exponence Morphology.PFM

/-! ### Old English HIERAN 'hear' (§2.2, Table 3) -/

section OldEnglish

/-- The weak verb HIERAN. -/
inductive Verb | hieran
  deriving DecidableEq, Fintype

/-- Mood, tense, person, and number features (decomposed). -/
inductive Feat | ind | sbj | imp | pres | past | p1 | p2 | p3 | sg | pl
  deriving DecidableEq, Fintype

open Verb Feat

/-- Block I (position i): the past-tense formative `-d-`. -/
def blockI : Block Verb String (Finset Feat) :=
  [ ⟨Finset.univ, {past}, .const (· ++ "d")⟩,
    identityDefault ]

/-- Block II (position ii): the theme vowel — `-o-` in the past plural,
`-e-` elsewhere in the past (the present-tense conditioning is not modelled). -/
def blockII : Block Verb String (Finset Feat) :=
  [ ⟨Finset.univ, {past, pl}, .const (· ++ "o")⟩,
    ⟨Finset.univ, {past}, .const (· ++ "e")⟩,
    identityDefault ]

/-- Block III (position iii): agreement and mood — `-st` (2sg indicative,
[stump-2020]'s rule (7)), `-þ` (3sg present indicative), `-aþ` (present plural),
`-n` (past plural). -/
def blockIII : Block Verb String (Finset Feat) :=
  [ ⟨Finset.univ, {ind, p2, sg}, .const (· ++ "st")⟩,
    ⟨Finset.univ, {ind, pres, p3, sg}, .const (· ++ "þ")⟩,
    ⟨Finset.univ, {pres, pl}, .const (· ++ "aþ")⟩,
    ⟨Finset.univ, {past, pl}, .const (· ++ "n")⟩,
    identityDefault ]

/-- The HIERAN paradigm function: stem `hīer` through Blocks I–III. -/
def hieranPF (σ : Finset Feat) : String :=
  paradigmFunction (fun _ ↦ "hīer") [blockI, blockII, blockIII] (hieran, σ)

/-- 1sg past indicative: `hīer` + `-d-` + `-e-` = `hīerde`. -/
example : hieranPF {ind, past, p1, sg} = "hīerde" := by decide

/-- 3sg past indicative: `hīerde` (theme `-e-`, no agreement suffix). -/
example : hieranPF {ind, past, p3, sg} = "hīerde" := by decide

/-- 2sg past indicative: `hīer` + `-d-` + `-e-` + `-st` = `hīerdest`. -/
example : hieranPF {ind, past, p2, sg} = "hīerdest" := by decide

/-- Plural past indicative: `hīer` + `-d-` + `-o-` + `-n` = `hīerdon`. -/
example : hieranPF {ind, past, pl} = "hīerdon" := by decide

/-- Plural present indicative: `hīer` + `-aþ` = `hīeraþ` (the theme vowel is
elided; elision is phonological and not modelled). -/
example : hieranPF {ind, pres, pl} = "hīeraþ" := by decide

/-- The 2sg imperative is the bare stem `hīer`, the Identity Function Default firing in every
block. -/
example : hieranPF {imp, p2, sg} = "hīer" := by decide

end OldEnglish

end Stump2020
