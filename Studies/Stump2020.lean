module

public import Linglib.Morphology.Paradigm.Function
public import Linglib.Morphology.Word.Features
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

open Verb

/-- The indicative property set of tense `t`, person `p` and number `n`. -/
def finite (t : UD.Tense) (p : Person) (n : Number) : Features :=
  .of (person := some p) (number := some n) (tense := some t) (mood := some .Ind)

/-- Block I (position i): the past-tense formative `-d-`. -/
def blockI : Block Verb String Features :=
  [ ⟨Finset.univ, .of (tense := some .Past), .const (· ++ "d")⟩,
    identityDefault ]

/-- Block II (position ii): the theme vowel — `-o-` in the past plural,
`-e-` elsewhere in the past (the present-tense conditioning is not modelled). -/
def blockII : Block Verb String Features :=
  [ ⟨Finset.univ, .of (number := some .plural) (tense := some .Past), .const (· ++ "o")⟩,
    ⟨Finset.univ, .of (tense := some .Past), .const (· ++ "e")⟩,
    identityDefault ]

/-- Block III (position iii): agreement and mood — `-st` (2sg indicative,
[stump-2020]'s rule (7)), `-þ` (3sg present indicative), `-aþ` (present plural),
`-n` (past plural). -/
def blockIII : Block Verb String Features :=
  [ ⟨Finset.univ, .of (person := some .second) (number := some .singular) (mood := some .Ind),
      .const (· ++ "st")⟩,
    ⟨Finset.univ, finite .Pres .third .singular, .const (· ++ "þ")⟩,
    ⟨Finset.univ, .of (number := some .plural) (tense := some .Pres), .const (· ++ "aþ")⟩,
    ⟨Finset.univ, .of (number := some .plural) (tense := some .Past), .const (· ++ "n")⟩,
    identityDefault ]

/-- The HIERAN paradigm function: stem `hīer` through Blocks I–III. -/
def hieranPF (σ : Features) : String :=
  paradigmFunction (fun _ ↦ "hīer") [blockI, blockII, blockIII] (hieran, σ)

/-- 1sg past indicative: `hīer` + `-d-` + `-e-` = `hīerde`. -/
example : hieranPF (finite .Past .first .singular) = "hīerde" := by decide

/-- 3sg past indicative: `hīerde` (theme `-e-`, no agreement suffix). -/
example : hieranPF (finite .Past .third .singular) = "hīerde" := by decide

/-- 2sg past indicative: `hīer` + `-d-` + `-e-` + `-st` = `hīerdest`. -/
example : hieranPF (finite .Past .second .singular) = "hīerdest" := by decide

/-- Plural past indicative: `hīer` + `-d-` + `-o-` + `-n` = `hīerdon`. -/
example : hieranPF (.of (number := some .plural) (tense := some .Past) (mood := some .Ind)) =
    "hīerdon" := by decide

/-- Plural present indicative: `hīer` + `-aþ` = `hīeraþ` (the theme vowel is
elided; elision is phonological and not modelled). -/
example : hieranPF (.of (number := some .plural) (tense := some .Pres) (mood := some .Ind)) =
    "hīeraþ" := by decide

/-- The 2sg imperative is the bare stem `hīer`, the Identity Function Default firing in every
block. -/
example : hieranPF (.of (person := some .second) (number := some .singular) (mood := some .Imp)) =
    "hīer" := by decide

end OldEnglish

end Stump2020
